/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.UnwindSetDiscrAndFnPtrMR

/-!
# Episode 2 Dual-Authority Correspondence (`MiniRustSpec` Authority):
# non-capturing closure function pointers (`ClosureFnPointer`) and their calls

Operational correspondence between the callee-directed closure semantics of
`Trusted.Rustc.V2026_06_01.MirSemantics` (`evalReifyFnPointer`,
`evalUnsafeFnPointer`, `evalFnPtrToPtr`, `checkClosureCalleeSig`,
`checkCalleeTargetCompatible`, `calleeOwnClosureShape?`, `evalCallTerminator`,
`evalTailCallTerminator`, the `const_eval_select` runtime-target helpers, all
reached through the real `stepMirFn`) and `MiniRustSpec.Interp` across **both
`Mach` (`BasicMemory<x86_64>`) and `MachTB` (`TreeBorrowsMemory<x86_64>`,
preserving `MachTB.wfLive`)**.

## The correspondence

`Trusted` reaches a non-capturing closure body through a function pointer by
*callee-directed* dispatch: the pointer's `FnPtrEntry` carries no closure flag;
the linked body is classified by its own environment parameter `_1`
(`calleeOwnClosureShape?`), and an indirect call enters it with a synthesized
zero-sized environment prepended (`synthesizeClosureEnvArg mode ptrBytes ::
argVals` into `_1 .. _{N+1}`), for the three receiver modes `Fn`
(`&{closure}`), `FnMut` (`&mut {closure}`), and `FnOnce` (`{closure}` by
value). MiniRust has no closure types: the same pointer denotes a `Function`
of the closure's user-visible arity `N` (`Machine::fn_ptrs`), called with `N`
arguments by `Terminator::Call` and left by `Terminator::Return`.

1. **Universal laws (§2)**, quantified over every memory, callee table, body,
   signature, and memory-polymorphic MiniRust machine:
   * `checkClosureCalleeSig_callee_directed`, `closureFnPointer_reify_callee_directed`:
     `ClosureFnPointer(Safe|Unsafe)` reification is decided by the linked body alone;
   * `ClosureFnPtrEntryRel` (the closure extension of `FnPtrEntryRel`) and
     `ClosureFnSigRel` (tying Trusted closure `_0` / `_2.._{N+1}` types to
     MiniRust `fn.locals[fn.ret]` and `fn.locals[fn.args]` via `translateTy`) with
     `closure_reify_establishes_entryRel_M`, `closureFnPtrEntryRel_call_arity`,
     `closure_coercion_widening_identity_general_mach_and_tb` (arbitrary
     `fn(fnIns) -> fnOut`, covering both `ClosureFnPointer(Safe)` +
     `UnsafeFnPointer` + `FnPtrToPtr` and direct `ClosureFnPointer(Unsafe)` +
     `FnPtrToPtr`, proving pointer identity `raw_c == raw_d` on `Mach` and
     `MachTB`), `closure_coercion_widening_identity_mach_and_tb`, the coupled
     two-sided call law `closure_indirect_call_correspondence_M` (connecting
     `s.memory`, the evaluated Trusted pointer `p`, `resolveCallTarget`,
     `fnFromPtrM`, and `createFrameM`), and the typed signature ABI-mismatch law
     `closure_typed_sig_call_correspondence_M` (universal return-type and
     argument-type transmutation UB lockstep across Trusted, `Mach`, and `MachTB`);
   * `closure_indirect_call_prepends_env`, `closure_indirect_tailCall_prepends_env`,
     `closure_entry_frame_binds_env_then_args`, and
     `constEvalSelect_closure_runtime_target_dispatch` (Trusted) against
     `minirust_createFrameM_arity_law`, `minirust_createFrameM_abi_mismatch_law`,
     `minirust_ptr_rel_eq_same_addr_M`, and `minirust_closure_call_return_tb_wfLive`
     (MiniRust);
   * fail-closed laws: `classifyOwnClosureEnvTy_by_upvars`, `closureFnPointer_reify_fail_closed`,
     `closure_indirect_call_fail_closed`, `closure_indirect_call_generic_unsupported`,
     `closure_direct_call_dispatches_unchanged`, and
     `closureFnPointer_normal_spelling_unsupported`.
2. **Concrete kernel-checked three-way witnesses (§4, §5)** on verbatim
   `rustc-capture` bodies (§0): `Fn`, `FnMut`, `FnOnce`, zero-argument,
   two-argument, `ClosureFnPointer(Unsafe)`, `ClosureFnPointer(Safe)` +
   `UnsafeFnPointer` + `FnPtrToPtr` (`raw_c == raw_d`), `TerminatorKind::TailCall`,
   mixed `fn`-item + closure coercion, `const_eval_select`, the difftest
   reproducer `pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27`
   (`__anneal_vt_driver_61873(35, 24) = 159` and `9147 : u32`, the value Miri
   reports), and the fail-closed negatives (capturing `u32`, capturing `()`,
   forged `(N + 1)`-argument calls, transmuted signature, `extern "C"`,
   `Safety` mismatch, generic closure under `R1`, direct call with explicit
   `&_env`).

## Divergences that are characterized, not hidden

* MiniRust erases function-pointer `Safety`, so a `Safety`-mismatched coercion
  (`.ub` in `Trusted`) has no MiniRust counterpart; a capturing closure has no
  function-pointer image at all (`rustc` rejects the coercion), so the
  capturing-closure faults are Trusted-only fail-closed laws.
* `Trusted` elides the `ClosureOnceShim` frame that `rustc` interposes for `Fn`
  and `FnMut` closures and passes the address `1` without provenance as the
  environment; MiniRust's function of arity `N` has no environment at all. The
  observable results agree because a non-capturing body never reads `_1`.

* In `closure_typed_sig_call_correspondence_M` the MiniRust-side mismatched
  types (`badMrRet`, `badMrArg`) are premises, not images of the Trusted
  transmuted types under `cfTranslateAbiTy`. The two checks genuinely differ on
  pointers: MiniRust `check_abi_compatibility` compares only the pointer
  metadata kind, so a transmuted `&u32` / `*const u64` argument is accepted by
  MiniRust while `Trusted` (`calleeParamTysMatch`) rejects it; for integers both
  require the same signedness and width. The law is therefore stated for the
  mismatches MiniRust also rejects.

## Why the earlier correspondence did not catch the reproducer

The earlier `C8` correspondence of `MiniRustSpec.UnwindSetDiscrAndFnPtrMR`
(`c8AllFiveMir`, the cached-reification witness) exercised
`ClosureFnPointer` only as a *coercion* with `callees := []`, on hand-built
zero-sized closure operands (`constZst (closureZstMirTy _)`, a `.closure _ []`
type written by hand), and never called the resulting pointer into a linked
closure body. Its premises were therefore satisfied by fixtures that
`rustc-capture` did not produce at the time: the captured closure type carried
the full generic-argument list instead of the upvar types (so the real cast
was `.ub`), closure bodies were not captured or linked, and the closure body's
MIR ABI (`argCount = N + 1` with the environment `_1`) was outside the proof's
scope. This module closes that gap structurally: every fixture is a verbatim
`rustc-capture` body, every positive witness links the closure bodies and
calls through the pointer, and the universal laws are stated on the linked
body's own shape. The `lean-miri` side of this postmortem is recorded in
`LeanMiriSpec.ClosureFnPtrLM`.

Strict import isolation: this module NEVER imports `Anneal.*`, `Miri.*`, or
`LeanMiriSpec.*` (verified by the trailing `#assert_closure_fn_ptr_mr_audit`).
-/

namespace MiniRustSpec.ClosureFnPtrMR

set_option Elab.async false

/-! ## §0. Verbatim `rustc-capture` Fixtures (shared with `LeanMiriSpec.ClosureFnPtrLM`)

Every definition of this section is the verbatim output of `rustc-capture`
(`Runtime(PostCleanup)` MIR captured with `-Zmir-opt-level=0`), copied without
modification from `tests/mir/ClosureFnPtrTests.lean`: the four bodies of the
difftest reproducer (`cfFx_finding_*`) and the closure matrix crate. The same
block, under the same names, is embedded in `LeanMiriSpec.ClosureFnPtrLM`. -/

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

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.Correspondence MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness MiniRustSpec.Correspondence.WideSliceDst
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR

/-! ## §1. Direct Trusted `stepMirFn` Runner

`cfRun` iterates the REAL `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`
(no shadow evaluator): every running step is literally a `stepMirFn` step
(`cfRunStep_of_step`, `cfRunStep_of_fail`, `cfRunStep_of_unsupported`). -/

/-- Normalized observation of one bounded Trusted `stepMirFn` execution. -/
inductive CfObs : Type where
  /-- Normal return of a scalar (`bits`, width in bytes). -/
  | scalar (bits size : Nat)
  /-- Normal return of a non-scalar value. -/
  | other
  | panic
  | abort
  | ub
  | unsupported
  /-- A pending external call to `defPath`. -/
  | ext (defPath : String)
  /-- Out of fuel or a pending interaction outside the observable domain. -/
  | stuck
  deriving DecidableEq, Repr

/-- State of a bounded Trusted `stepMirFn` execution. -/
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

/-- Execute `stepMirFn` directly for up to `fuel` steps and return the
normalized observation. -/
def cfRun (body : CapturedMir) (fuel : Nat) (s : MachineState) : CfObs :=
  match Nat.repeat (cfRunStep body) fuel (.running s) with
  | .done o => o
  | .running _ => .stuck

/-- Initial Trusted state of `body` on `args` with linked `callees`
(`initMachineStateWithCallees`, see `cfInit_eq_initMachineStateWithCallees`). -/
def cfInit (body : CapturedMir) (args : List MirSemantics.Value) (callees : List CapturedMir) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocalsAux 0 body.localDecls args },
    memory := { emptyMemory with nextAllocId := length body.allocations, globals := body.allocations,
                                 callees := callees, traitImpls := body.traitImpls } }

/-- `cfInit` is the Trusted initial state `initMachineStateWithCallees` whenever
at least one callee is linked. -/
theorem cfInit_eq_initMachineStateWithCallees (body : CapturedMir) (args : List MirSemantics.Value)
    (c : CapturedMir) (cs : List CapturedMir) :
    cfInit body args (c :: cs) = initMachineStateWithCallees body args (c :: cs) := rfl

/-- `cfInit` with pre-registered function-pointer entries `fnPtrs` (a pointer
obtained elsewhere, e.g. forged or passed in as an argument). -/
def cfInitPtrs (body : CapturedMir) (args : List MirSemantics.Value) (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry) : MachineState :=
  { frame := (cfInit body args callees).frame,
    memory := { (cfInit body args callees).memory with fnPtrs := fnPtrs } }

/-- A running runner step is exactly a `stepMirFn` step. -/
theorem cfRunStep_of_step (body : CapturedMir) (s s' : MachineState)
    (h : stepMirFn body s = MirStepNode.step s') : cfRunStep body (.running s) = .running s' := by
  simp only [cfRunStep, h]; rfl

/-- The runner reports `.ub` exactly on a `stepMirFn` UB fault. -/
theorem cfRunStep_of_fail (body : CapturedMir) (s : MachineState)
    (h : stepMirFn body s = MirStepNode.fail .ub) : cfRunStep body (.running s) = .done .ub := by
  simp only [cfRunStep, h]; rfl

/-- The runner reports `.unsupported` exactly on a `stepMirFn` unsupported fault. -/
theorem cfRunStep_of_unsupported (body : CapturedMir) (s : MachineState)
    (h : stepMirFn body s = MirStepNode.unsupported) : cfRunStep body (.running s) = .done .unsupported := by
  simp only [cfRunStep, h]; rfl

/-- A `u32` Trusted value. -/
def cfU32V (n : Nat) : MirSemantics.Value := .scalar ⟨n, 4⟩

/-- Numeric tag of a closure-shape classification (for kernel-decided witnesses). -/
def cfShapeTag : Option CalleeClosureShape → Nat
  | none => 0
  | some (.nonCapturing .sharedRef) => 1
  | some (.nonCapturing .mutRef) => 2
  | some (.nonCapturing .byValue) => 3
  | some .capturing => 4

/-- `cfShapeTag` is injective, so a kernel-decided tag determines the shape. -/
theorem cfShapeTag_inj : ∀ {a b : Option CalleeClosureShape}, cfShapeTag a = cfShapeTag b → a = b
  | none, none, _ => rfl
  | none, some (.nonCapturing .sharedRef), h | none, some (.nonCapturing .mutRef), h
  | none, some (.nonCapturing .byValue), h | none, some .capturing, h => by cases h
  | some (.nonCapturing .sharedRef), b, h => by
    match b, h with
    | some (.nonCapturing .sharedRef), _ => rfl
  | some (.nonCapturing .mutRef), b, h => by
    match b, h with
    | some (.nonCapturing .mutRef), _ => rfl
  | some (.nonCapturing .byValue), b, h => by
    match b, h with
    | some (.nonCapturing .byValue), _ => rfl
  | some .capturing, b, h => by
    match b, h with
    | some .capturing, _ => rfl
/-! ## §2. Universal Operational Laws (`Trusted` callee-directed Design A′ ↔ MiniRust `N`-argument functions)

The laws of this section are quantified over every memory, callee table,
closure body, function-pointer signature, and MiniRust machine (`Mach` and
`MachTB` through the memory-polymorphic `Machine M`). They never mention a flag
on `FnPtrEntry`: a function pointer is a *closure* pointer exactly when the
linked body it names is closure-shaped (`calleeOwnClosureShape?`). -/

/-- The three `PointerCoercion::ClosureFnPointer` coercion tags that
`Trusted.MirSemantics` executes (`isClosureFnPointerCoercion`). -/
def IsClosureCoercionTag (ck : String) : Prop :=
  ck = "ClosureFnPointer" ∨ ck = "ClosureFnPointer(Safe)" ∨ ck = "ClosureFnPointer(Unsafe)"

/-- Every closure coercion tag selects the closure branch of
`evalReifyFnPointer` (and none is the `UnsafeFnPointer` widening tag). -/
theorem closureCoercionTag_dispatch_flags {ck : String} (h : IsClosureCoercionTag ck) :
    isClosureFnPointerCoercion ck = true ∧ isReifyFnPointerCoercion ck = true ∧
    stringEq ck "UnsafeFnPointer" = false := by
  rcases h with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩

/-- `n ≠ n + 1` for the kernel `Nat.beq` used by `checkClosureTargetCompatible`. -/
theorem nat_beq_self_succ_false : ∀ n : Nat, Nat.beq n (Nat.succ n) = false
  | 0 => rfl
  | n + 1 => nat_beq_self_succ_false n

/-- **Callee-directed coercion check (`checkClosureCalleeSig`), exhaustive
characterization for a linked body.** For a body `c` linked under `p`:
a non-closure body is `.ub`; a non-generic *capturing* closure body is `.ub`
(C10); every *generic* closure body (capturing or not) is `.unsupported`, never
`.ub` (C5); a non-generic non-capturing closure body is `.ok` exactly when its
own ABI is Rust, `argCount = N + 1`, and `_0 :: _1 :: params` match the
pointer signature; and any non-Rust target ABI is `.ub`. -/
theorem checkClosureCalleeSig_callee_directed (callees : List CapturedMir) (p : DefPath)
    (fnIns : List RigidTy) (fnOut : RigidTy) (c : CapturedMir)
    (hLinked : findCallee? callees p = some c) :
    (calleeOwnClosureShape? c = none → checkClosureCalleeSig callees p fnIns fnOut .rust = .ub) ∧
    (calleeOwnClosureShape? c = some .capturing → c.typeParamCount = 0 →
      checkClosureCalleeSig callees p fnIns fnOut .rust = .ub) ∧
    (∀ sh k, calleeOwnClosureShape? c = some sh → c.typeParamCount = k + 1 →
      checkClosureCalleeSig callees p fnIns fnOut .rust = .unsupported) ∧
    (∀ mode, calleeOwnClosureShape? c = some (.nonCapturing mode) → c.typeParamCount = 0 →
      checkClosureCalleeSig callees p fnIns fnOut .rust =
        (match Bool.and (callConvEq c.fnAbi.conv .rust)
            (Bool.and (Nat.beq c.argCount (Nat.succ (length fnIns)))
              (closureCalleeDeclsCompatible [] c.localDecls (length fnIns) fnIns fnOut)) with
         | true => ClosureCoercionCheck.ok
         | false => ClosureCoercionCheck.ub)) ∧
    (∀ abi, callConvEq abi .rust = false → checkClosureCalleeSig callees p fnIns fnOut abi = .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; unfold checkClosureCalleeSig; simp only [hLinked, h]
  · intro h ht; unfold checkClosureCalleeSig; simp only [hLinked, h, ht]
  · intro sh k h ht; unfold checkClosureCalleeSig
    cases sh <;> simp only [hLinked, h, ht]
  · intro mode h ht; unfold checkClosureCalleeSig; simp only [hLinked, h, ht]
    generalize Bool.and (callConvEq c.fnAbi.conv CallConv.rust)
      (Bool.and (Nat.beq c.argCount (Nat.succ (length fnIns)))
        (closureCalleeDeclsCompatible [] c.localDecls (length fnIns) fnIns fnOut)) = b
    cases b <;> rfl
  · intro abi h; unfold checkClosureCalleeSig; simp only [h]

/-- An unlinked closure path coerces (as for unlinked `fn` items); the pointer
then only reaches the closure through an external call. -/
theorem checkClosureCalleeSig_unlinked_ok (callees : List CapturedMir) (p : DefPath)
    (fnIns : List RigidTy) (fnOut : RigidTy) (h : findCallee? callees p = none) :
    checkClosureCalleeSig callees p fnIns fnOut .rust = .ok := by
  unfold checkClosureCalleeSig; simp only [h]

/-- **Universal `ClosureFnPointer(Safe|Unsafe)` reification law.** For every
closure coercion tag, a zero-sized closure value whose operand type is the
non-capturing closure type `{closure dp}` reifies exactly as the
callee-directed check `checkClosureCalleeSig` of the linked body decides:
`.ub`, `.unsupported`, or the interned function pointer
(`internFnPtr mem dp [] (some sig)`, no closure flag on the `FnPtrEntry`). -/
theorem closureFnPointer_reify_callee_directed (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (ck : String)
    (dp : DefPath) (li : Nat) (fnIns : List RigidTy) (fnOut : RigidTy) (fnSaf : Safety) (fnAbi : CallConv)
    (zstVal : MirSemantics.Value) (hCk : IsClosureCoercionTag ck)
    (hZst : zstVal = .unit ∨ zstVal = .aggregate 0 [])
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      (callStack := mem.callStack) = .ok zstVal locals')
    (hAbi : callConvEq fnAbi .rustIntrinsic = false)
    (hSaf : reifyCoercionSafetyCompatible ck fnSaf = true)
    (hTy : operandTy decls layouts op = some { kind := .closure dp [], layoutIdx := li }) :
    evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts =
      (match checkClosureCalleeSig mem.callees dp fnIns fnOut fnAbi with
       | .ub => RvalueEvalResult.ub
       | .unsupported => RvalueEvalResult.unsupported
       | .ok =>
         RvalueEvalResult.ok
           (.ptr { allocId := (internFnPtr mem dp [] (some (.fnPtr fnIns fnOut fnSaf fnAbi))).1,
                   offsetBytes := 0 } 8)
           locals' (internFnPtr mem dp [] (some (.fnPtr fnIns fnOut fnSaf fnAbi))).2) := by
  obtain ⟨hC, hR, hNU⟩ := closureCoercionTag_dispatch_flags hCk
  show evalReifyFnPointer locals op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 } mem decls layouts ck = _
  unfold evalReifyFnPointer
  rcases hZst with rfl | rfl <;>
    simp only [hR, hNU, hOp, hAbi, Bool.not_false, hSaf, Bool.and_self, hTy, hC,
      extractReifyCoercionTarget?] <;>
    cases checkClosureCalleeSig mem.callees dp fnIns fnOut fnAbi <;> rfl

/-- **Universal fail-closed coercion law (C10, ABI, safety, C5).** For every
closure coercion tag and target `fn` pointer type:
1. a capturing closure *value* (`.aggregate 0 (v :: vs)`) is `.ub`;
2. a capturing closure *type* (`{closure dp (u :: us)}`, any upvar types, in
   particular the zero-sized `()`) is `.ub` even though its value is zero-sized;
3. a `rust-intrinsic` target ABI is `.ub`;
4. a coercion tag whose `Safety` disagrees with the target pointer is `.ub`;
5. any non-Rust target ABI (`extern "C"`, ...) is `.ub`;
6. a linked *generic* closure body is `.unsupported`, never `.ub` (C5). -/
theorem closureFnPointer_reify_fail_closed (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (ck : String)
    (fnIns : List RigidTy) (fnOut : RigidTy) (fnSaf : Safety) (fnAbi : CallConv)
    (hCk : IsClosureCoercionTag ck) :
    (∀ v0 vs, evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok (.aggregate 0 (v0 :: vs)) locals' →
      evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts = .ub) ∧
    (∀ zstVal dp u us li, (zstVal = .unit ∨ zstVal = .aggregate 0 []) →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok zstVal locals' →
      operandTy decls layouts op = some { kind := .closure dp (u :: us), layoutIdx := li } →
      evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts = .ub) ∧
    (∀ zstVal, (zstVal = .unit ∨ zstVal = .aggregate 0 []) →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok zstVal locals' →
      callConvEq fnAbi .rustIntrinsic = true →
      evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts = .ub) ∧
    (∀ zstVal, (zstVal = .unit ∨ zstVal = .aggregate 0 []) →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok zstVal locals' →
      reifyCoercionSafetyCompatible ck fnSaf = false →
      evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts = .ub) ∧
    (∀ zstVal dp li, (zstVal = .unit ∨ zstVal = .aggregate 0 []) →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok zstVal locals' →
      callConvEq fnAbi .rustIntrinsic = false → reifyCoercionSafetyCompatible ck fnSaf = true →
      operandTy decls layouts op = some { kind := .closure dp [], layoutIdx := li } →
      callConvEq fnAbi .rust = false →
      evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts = .ub) ∧
    (∀ zstVal dp li c sh k, (zstVal = .unit ∨ zstVal = .aggregate 0 []) →
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok zstVal locals' →
      fnAbi = .rust → reifyCoercionSafetyCompatible ck fnSaf = true →
      operandTy decls layouts op = some { kind := .closure dp [], layoutIdx := li } →
      findCallee? mem.callees dp = some c → calleeOwnClosureShape? c = some sh →
      c.typeParamCount = k + 1 →
      evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 })
        mem decls layouts = .unsupported) := by
  obtain ⟨hC, hR, hNU⟩ := closureCoercionTag_dispatch_flags hCk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v0 vs hOp
    show evalReifyFnPointer locals op _ mem decls layouts ck = .ub
    unfold evalReifyFnPointer; simp only [hR, hNU, hOp]
  · intro zstVal dp u us li hZst hOp hTy
    show evalReifyFnPointer locals op _ mem decls layouts ck = .ub
    unfold evalReifyFnPointer
    rcases hZst with rfl | rfl <;>
      cases hG : Bool.and (Bool.not (callConvEq fnAbi .rustIntrinsic)) (reifyCoercionSafetyCompatible ck fnSaf) <;>
      simp only [hR, hNU, hOp, hG, hTy, hC, extractReifyCoercionTarget?]
  · intro zstVal hZst hOp hI
    show evalReifyFnPointer locals op _ mem decls layouts ck = .ub
    unfold evalReifyFnPointer
    rcases hZst with rfl | rfl <;> simp only [hR, hNU, hOp, hI, Bool.not_true, Bool.false_and]
  · intro zstVal hZst hOp hS
    show evalReifyFnPointer locals op _ mem decls layouts ck = .ub
    unfold evalReifyFnPointer
    rcases hZst with rfl | rfl <;> simp only [hR, hNU, hOp, hS, Bool.and_false]
  · intro zstVal dp li hZst hOp hAbi hSaf hTy hNR
    rw [closureFnPointer_reify_callee_directed locals locals' op mem decls layouts ck dp li fnIns fnOut fnSaf
      fnAbi zstVal hCk hZst hOp hAbi hSaf hTy]
    have : checkClosureCalleeSig mem.callees dp fnIns fnOut fnAbi = .ub := by
      unfold checkClosureCalleeSig; simp only [hNR]
    rw [this]
  · intro zstVal dp li c sh k hZst hOp hAbi hSaf hTy hLinked hSh hT
    subst hAbi
    rw [closureFnPointer_reify_callee_directed locals locals' op mem decls layouts ck dp li fnIns fnOut fnSaf
      .rust zstVal hCk hZst hOp rfl hSaf hTy]
    rw [(checkClosureCalleeSig_callee_directed mem.callees dp fnIns fnOut c hLinked).2.2.1 sh k hSh hT]

/-- **The `"ClosureFnPointer(Normal)"` spelling boundary.** `Trusted` does not
recognise the tag (it is not one of the three tags `rustc-capture` emits for
`PointerCoercion::ClosureFnPointer(hir::Safety)`), so the cast is
`.unsupported`, never `.ub` and never a successful reification. -/
theorem closureFnPointer_normal_spelling_unsupported (locals : List LocalSlot) (op : MirAst.Operand)
    (targetTy : MirAst.Ty) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    isClosureFnPointerCoercion "ClosureFnPointer(Normal)" = false ∧
    evalRvalue locals (.cast (.pointerCoercion "ClosureFnPointer(Normal)") op targetTy) mem decls layouts =
      .unsupported := ⟨rfl, rfl⟩

/-- Entry locals of a body with at least `_0` and `_1` entered with arguments
`env :: argVals`: `_0` is live and uninitialized, `_1` holds `env`, and the
remaining parameters are bound from `argVals`. -/
theorem closure_entry_locals_layout (c : CapturedMir) (env : MirSemantics.Value)
    (argVals : List MirSemantics.Value) (d0 d1 : MirAst.LocalDecl) (rest : List MirAst.LocalDecl)
    (hDecls : c.localDecls = d0 :: d1 :: rest) :
    initLocals c (env :: argVals) = .uninit :: .init env :: initLocalsAux 1 rest argVals := by
  unfold initLocals; rw [hDecls]; rfl

/-- The `i`-th caller argument lands in parameter slot `i` of
`initLocalsAux (k + 1)`. -/
theorem initLocalsAux_succ_get? : ∀ (decls : List MirAst.LocalDecl) (k : Nat)
    (args : List MirSemantics.Value) (i : Nat) (v : MirSemantics.Value),
    get? args i = some v → i < length decls →
    get? (initLocalsAux (k + 1) decls args) i = some (.init v)
  | [], _, _, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | _ :: _, _, [], i, _, hget, _ => by cases i <;> cases hget
  | _ :: _, _, a :: _, 0, v, hget, _ => by cases hget; rfl
  | _ :: ds, k, _ :: as, i + 1, v, hget, hlt =>
    initLocalsAux_succ_get? ds k as i v hget (Nat.lt_of_succ_lt_succ hlt)

/-- **Callee-directed ZST-environment prepend: frame layout.** Entering a
closure body `c` (`_0 :: _1 :: params`) with the synthesized environment
prepended binds `_1` to `synthesizeClosureEnvArg mode ptrBytes` and the `i`-th
caller argument to `_{i + 2}`: the caller's `N` arguments occupy
`_2 .. _{N + 1}`. -/
theorem closure_entry_frame_binds_env_then_args (c : CapturedMir) (mode : ClosureEnvMode)
    (argVals : List MirSemantics.Value) (d0 d1 : MirAst.LocalDecl) (rest : List MirAst.LocalDecl)
    (hDecls : c.localDecls = d0 :: d1 :: rest) :
    let env := synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts)
    get? (initLocals c (env :: argVals)) 0 = some .uninit ∧
    get? (initLocals c (env :: argVals)) 1 = some (.init env) ∧
    (∀ i v, get? argVals i = some v → i < length rest →
      get? (initLocals c (env :: argVals)) (i + 2) = some (.init v)) ∧
    (mode = .sharedRef ∨ mode = .mutRef → env = .scalar ⟨1, layoutPointerBytes c.layouts⟩) ∧
    (mode = .byValue → env = .aggregate 0 []) := by
  intro env
  rw [closure_entry_locals_layout c env argVals d0 d1 rest hDecls]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro i v hget hlt
    exact initLocalsAux_succ_get? rest 0 argVals i v hget hlt
  · rintro (rfl | rfl) <;> rfl
  · rintro rfl; rfl

/-- **Universal indirect closure call law (`TerminatorKind.call`, callee-directed
ZST-environment prepend).** If the call target resolves *indirectly* (through a
function pointer) to a linked body `c` whose own environment parameter
classifies it as a non-capturing closure body
(`calleeOwnClosureShape? c = some (.nonCapturing mode)`), and the pointer
signature is compatible (`checkClosureTargetCompatible`: Rust ABI,
`c.argCount = N + 1`, `_0 :: _1 :: params` match), then BOTH the stepper's
`evalTerminator` arm and `evalCallTerminator` enter `c` with
`synthesizeClosureEnvArg mode ptrBytes :: argVals`, for all three receiver
modes. -/
theorem closure_indirect_call_prepends_env (s : MachineState) (callerBody : CapturedMir)
    (func : MirAst.Operand) (argOps : List MirAst.Operand) (dest : MirAst.Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (span : String) (target : ResolvedCallTarget)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value) (c : CapturedMir)
    (mode : ClosureEnvMode)
    (hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
      .ok target localsAfterFunc)
    (hInd : target.isIndirect = true)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hLook : lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs
      s.memory.traitImpls = some c)
    (hShape : calleeOwnClosureShape? c = some (.nonCapturing mode))
    (hCompat : checkClosureTargetCompatible target c (length argVals) = true) :
    evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals' dest targetBb c
        (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) unwind) ∧
    evalCallTerminator s func argOps dest (some targetBb) unwind (some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals' dest targetBb c
        (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) unwind) ∧
    (pushCalleeFrame s callerBody locals' dest targetBb c
        (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) unwind).frame.locals =
      initLocals c (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) ∧
    (pushCalleeFrame s callerBody locals' dest targetBb c
        (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) unwind).memory.activeCallee =
      some c := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [MirSemantics.evalTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, checkCalleeTargetCompatible, calleeEntryArgs,
      hInd, hShape, hCompat]
  · simp only [evalCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, checkCalleeTargetCompatible,
      calleeEntryArgs, hInd, hShape, hCompat]

/-- **Universal indirect closure `TerminatorKind.tailCall` law.** Under the
same callee-directed premises (and no frame-deallocation protector conflict),
`evalTailCallTerminator` (which is the stepper's `.tailCall` arm) replaces the
current frame by `c` entered with the synthesized environment prepended. -/
theorem closure_indirect_tailCall_prepends_env (s : MachineState) (callerBody : CapturedMir)
    (func : MirAst.Operand) (argOps : List MirAst.Operand) (span : String) (target : ResolvedCallTarget)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value) (c : CapturedMir)
    (mode : ClosureEnvMode)
    (hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
      .ok target localsAfterFunc)
    (hInd : target.isIndirect = true)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hProt : hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
      (length s.memory.callStack) (length s.frame.locals) = false)
    (hLook : lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs
      s.memory.traitImpls = some c)
    (hShape : calleeOwnClosureShape? c = some (.nonCapturing mode))
    (hCompat : checkClosureTargetCompatible target c (length argVals) = true) :
    evalTerminator s { kind := .tailCall func argOps, span := span } (some callerBody) =
      evalTailCallTerminator s func argOps (some callerBody) ∧
    evalTailCallTerminator s func argOps (some callerBody) =
      MirStepNode.step (enterTailCalleeFrame
        (tailCalleeEntryMemory s.memory.callStack
          { s.memory with borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack) (length s.frame.locals) }
          (length s.frame.locals)
          (length (initLocals c (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals))))
        c (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals)) := by
  refine ⟨rfl, ?_⟩
  simp only [evalTailCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hProt, hLook, checkCalleeTargetCompatible,
    calleeEntryArgs, hInd, hShape, hCompat]

/-- **Universal fail-closed indirect call law (C10, C5, forged `(N + 1)`-arity).**
For an *indirect* call (and tail call) whose target resolves to a linked body `c`:
1. a *capturing* closure body faults `.ub` for EVERY argument count (so a
   forged `(N + 1)`-argument pointer passing the environment explicitly also
   faults), whether its upvars are zero-sized or not;
2. a non-capturing closure body called with as many arguments as it has
   parameters (the forged `(N + 1)`-argument call that passes `_1`
   explicitly) faults `.ub`;
3. a non-capturing closure body whose own ABI is not Rust faults `.ub`. -/
theorem closure_indirect_call_fail_closed (s : MachineState) (callerBody : CapturedMir)
    (func : MirAst.Operand) (argOps : List MirAst.Operand) (dest : MirAst.Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (span : String) (target : ResolvedCallTarget)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value) (c : CapturedMir)
    (hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
      .ok target localsAfterFunc)
    (hInd : target.isIndirect = true)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hLook : lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs
      s.memory.traitImpls = some c) :
    (calleeOwnClosureShape? c = some .capturing ∨
      (∃ mode, calleeOwnClosureShape? c = some (.nonCapturing mode) ∧ length argVals = c.argCount) ∨
      (∃ mode, calleeOwnClosureShape? c = some (.nonCapturing mode) ∧ callConvEq c.fnAbi.conv .rust = false) →
      checkCalleeTargetCompatible target c (length argVals) = false ∧
      evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
        MirStepNode.fail .ub ∧
      evalCallTerminator s func argOps dest (some targetBb) unwind (some callerBody) = MirStepNode.fail .ub ∧
      evalCallTerminator s func argOps dest none unwind (some callerBody) = MirStepNode.fail .ub ∧
      (hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
          (length s.memory.callStack) (length s.frame.locals) = false →
        evalTailCallTerminator s func argOps (some callerBody) = MirStepNode.fail .ub)) := by
  intro hBad
  have hFalse : checkCalleeTargetCompatible target c (length argVals) = false := by
    rcases hBad with hCap | ⟨mode, hSh, hLen⟩ | ⟨mode, hSh, hConv⟩
    · simp only [checkCalleeTargetCompatible, hInd, hCap]
    · simp only [checkCalleeTargetCompatible, hInd, hSh, checkClosureTargetCompatible, hLen,
        nat_beq_self_succ_false, Bool.false_and, Bool.and_false]
    · simp only [checkCalleeTargetCompatible, hInd, hSh, checkClosureTargetCompatible, hConv, Bool.false_and]
  refine ⟨hFalse, ?_, ?_, ?_, ?_⟩
  · simp only [MirSemantics.evalTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hFalse]
  · simp only [evalCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hFalse]
  · simp only [evalCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hFalse]
  · intro hProt
    simp only [evalTailCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hProt, hLook, hFalse]

/-- **Universal C5 law at the call site.** An indirect call (or tail call)
whose pointer names a linked *generic* closure body — `lookupCallee` fails on
the type-argument arity because the closure type carries no parent generic
arguments — reports `.unsupported`, never `.ub` and never an external call. -/
theorem closure_indirect_call_generic_unsupported (s : MachineState) (callerBody : CapturedMir)
    (func : MirAst.Operand) (argOps : List MirAst.Operand) (dest : MirAst.Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (span : String) (target : ResolvedCallTarget)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value)
    (hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
      .ok target localsAfterFunc)
    (hInd : target.isIndirect = true)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hLook : lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs
      s.memory.traitImpls = none)
    (hGen : isGenericClosureArityMismatch s.memory.callees target.defPath target.typeArgs = true) :
    evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
      MirStepNode.unsupported ∧
    evalCallTerminator s func argOps dest (some targetBb) unwind (some callerBody) = MirStepNode.unsupported ∧
    evalCallTerminator s func argOps dest none unwind (some callerBody) = MirStepNode.unsupported ∧
    (hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
        (length s.memory.callStack) (length s.frame.locals) = false →
      evalTailCallTerminator s func argOps (some callerBody) = MirStepNode.unsupported) := by
  have hDiv : isDirectExactDivTarget target = false := by
    simp only [isDirectExactDivTarget, hInd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [MirSemantics.evalTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hDiv, hInd, hGen]
  · simp only [evalCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hDiv, hInd, hGen, Bool.and_self]
  · simp only [evalCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hInd, hGen]
  · intro hProt
    simp only [evalTailCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hProt, hLook, hInd, hGen, Bool.and_self]

/-- **Universal direct-call law (C11).** A *direct* call
(`target.isIndirect = false`) to a linked body — in particular to a closure
body of any shape, capturing or not, passing the environment `&_env`
explicitly — is never rejected by the closure gate and enters the body with
the evaluated arguments unchanged (no synthesized environment). -/
theorem closure_direct_call_dispatches_unchanged (s : MachineState) (callerBody : CapturedMir)
    (func : MirAst.Operand) (argOps : List MirAst.Operand) (dest : MirAst.Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (span : String) (target : ResolvedCallTarget)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value) (c : CapturedMir)
    (hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
      .ok target localsAfterFunc)
    (hDir : target.isIndirect = false)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hLook : lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs
      s.memory.traitImpls = some c) :
    checkCalleeTargetCompatible target c (length argVals) = true ∧
    calleeEntryArgs target c argVals = argVals ∧
    evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals' dest targetBb c argVals unwind) ∧
    evalCallTerminator s func argOps dest (some targetBb) unwind (some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals' dest targetBb c argVals unwind) := by
  have hC : checkCalleeTargetCompatible target c (length argVals) = true := by
    simp only [checkCalleeTargetCompatible, hDir]
  have hE : calleeEntryArgs target c argVals = argVals := by simp only [calleeEntryArgs, hDir]
  refine ⟨hC, hE, ?_, ?_⟩
  · simp only [MirSemantics.evalTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hC, hE]
  · simp only [evalCallTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hC, hE]

/-- **Universal `const_eval_select` closure runtime-target dispatch law.** For
the runtime target `rtTarget` of an inline `core::intrinsics::const_eval_select`
resolved to a linked body `c` and called with the `N` unpacked tuple arguments:
* a non-capturing closure body is entered with the synthesized environment
  prepended (`constEvalSelectEntryArgs`), and is compatible exactly when an
  *indirect* target passes `checkClosureTargetCompatible` or a *direct* target
  has the Rust ABI and `c.argCount = N + 1`;
* a capturing closure body is never compatible (C10);
* a linked generic closure body is not resolved as a direct closure target
  (`nonGenericClosureTarget? = none`, C5), while an unlinked or non-generic
  one is. -/
theorem constEvalSelect_closure_runtime_target_dispatch (rtTarget : ResolvedCallTarget) (c : CapturedMir)
    (unpackedArgs : List MirSemantics.Value) (callees : List CapturedMir) (dp : DefPath) :
    (∀ mode, calleeOwnClosureShape? c = some (.nonCapturing mode) →
      constEvalSelectEntryArgs c unpackedArgs =
        synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: unpackedArgs ∧
      (rtTarget.isIndirect = true →
        constEvalSelectCalleeCompatible rtTarget c (length unpackedArgs) =
          checkClosureTargetCompatible rtTarget c (length unpackedArgs)) ∧
      (rtTarget.isIndirect = false →
        constEvalSelectCalleeCompatible rtTarget c (length unpackedArgs) =
          Bool.and (callConvEq c.fnAbi.conv .rust) (Nat.beq c.argCount (Nat.succ (length unpackedArgs))))) ∧
    (calleeOwnClosureShape? c = some .capturing →
      constEvalSelectCalleeCompatible rtTarget c (length unpackedArgs) = false ∧
      constEvalSelectEntryArgs c unpackedArgs = unpackedArgs) ∧
    (calleeOwnClosureShape? c = none → constEvalSelectEntryArgs c unpackedArgs = unpackedArgs) ∧
    (findCallee? callees dp = none → nonGenericClosureTarget? callees dp = some (dp, [])) ∧
    (∀ sh, findCallee? callees dp = some c → calleeOwnClosureShape? c = some sh →
      (c.typeParamCount = 0 → nonGenericClosureTarget? callees dp = some (dp, [])) ∧
      (∀ k, c.typeParamCount = k + 1 → nonGenericClosureTarget? callees dp = none)) ∧
    (findCallee? callees dp = some c → calleeOwnClosureShape? c = none →
      nonGenericClosureTarget? callees dp = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro mode h
    refine ⟨by simp only [constEvalSelectEntryArgs, h], ?_, ?_⟩
    · intro hI; simp only [constEvalSelectCalleeCompatible, h, hI]
    · intro hD; simp only [constEvalSelectCalleeCompatible, h, hD]
  · intro h
    exact ⟨by simp only [constEvalSelectCalleeCompatible, h], by simp only [constEvalSelectEntryArgs, h]⟩
  · intro h; simp only [constEvalSelectEntryArgs, h]
  · intro h; simp only [nonGenericClosureTarget?, h]
  · intro sh hL hS
    exact ⟨fun ht => by simp only [nonGenericClosureTarget?, hL, hS, ht],
      fun k ht => by simp only [nonGenericClosureTarget?, hL, hS, ht]⟩
  · intro hL hS; simp only [nonGenericClosureTarget?, hL, hS]

/-- Memory after `internFnPtr` registers a fresh function-pointer entry for
`dp` with signature `sig`. The entry carries a `defPath`, type arguments, and
the pointer signature — and no closure flag. -/
def cfInternedMem (mem : MirSemantics.Memory) (dp : DefPath) (sig : RigidTy) : MirSemantics.Memory :=
  { mem with fnPtrs := { allocId := nextFnPtrAllocId mem.fnPtrs, defPath := dp, typeArgs := [], fnSig := some sig } :: mem.fnPtrs }

/-- The function pointer `internFnPtr` returns for a fresh entry. -/
def cfInternedPtr (mem : MirSemantics.Memory) : ProvenancePtr :=
  { allocId := nextFnPtrAllocId mem.fnPtrs, offsetBytes := 0 }

/-- **Callee-directed closure extension of `FnPtrEntryRel`.** Couples a Trusted
function pointer `(mem, p)` with a MiniRust machine `m` whose function-pointer
table maps `fnNm` to `(addr, prov)`:
* `entry`: the base relation `FnPtrEntryRel` (`UnwindSetDiscrAndFnPtrMR`);
* `fnEntry`/`linked`/`shape`/`nonGeneric`: the Trusted `FnPtrEntry` at
  `p.allocId` names a linked, non-generic body `c` that is closure-shaped by
  its OWN environment parameter (`calleeOwnClosureShape? c =
  some (.nonCapturing mode)`); the `FnPtrEntry` itself carries no closure flag;
* `trustedArity`: `c` has `n + 1` parameters (environment `_1` plus `n`
  declared parameters);
* `mrResolve`/`mrArity`/`mrConv`: MiniRust resolves the pointer
  (`Machine::fn_from_ptr`) to a `Function` of user-visible arity `n` with the
  Rust calling convention. -/
structure ClosureFnPtrEntryRel {M : Type} [Gen.Memory M] [MemoryOps M] (mem : MirSemantics.Memory)
    (p : ProvenancePtr) (m : Machine M) (fnNm : Gen.FnName) (addr : Nat)
    (prov : Option (Gen.Memory.Provenance M)) (c : CapturedMir) (mode : ClosureEnvMode)
    (fn : Gen.Function) (n : Nat) : Prop where
  entry : FnPtrEntryRel mem p m fnNm addr prov
  fnEntry : ∃ e, lookupFnPtr mem.fnPtrs p.allocId = some e ∧ e.defPath = c.defPath ∧ e.typeArgs = []
  linked : findCallee? mem.callees c.defPath = some c
  shape : calleeOwnClosureShape? c = some (.nonCapturing mode)
  nonGeneric : c.typeParamCount = 0
  trustedArity : c.argCount = n + 1
  mrResolve : fnFromPtrM m (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok fn
  mrArity : fn.args.length = n
  mrConv : fn.calling_convention = .Rust

/-- **Universal coercion correspondence (`Mach` & `MachTB`): a
`ClosureFnPointer(Safe|Unsafe)` cast establishes `ClosureFnPtrEntryRel`.** For
every closure coercion tag, signature `fn(fnIns) -> fnOut`, receiver mode, and
memory-polymorphic MiniRust machine `m`: when the linked body `c` of the
non-capturing closure type `{closure dp}` is a non-generic, Rust-ABI closure
body with `argCount = N + 1` whose `_0 :: _1 :: params` match the signature,
Trusted reifies a fresh function pointer (no closure flag), MiniRust evaluates
`Constant::FnPointer fnNm` without changing the machine (so `MachTB.wfLive` is
trivially preserved), and the two pointers are related by
`ClosureFnPtrEntryRel` to a MiniRust function of arity `N`. -/
theorem closure_reify_establishes_entryRel_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals locals' : List LocalSlot) (op : MirAst.Operand) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (ck : String) (dp : DefPath) (li : Nat)
    (fnIns : List RigidTy) (fnOut : RigidTy) (fnSaf : Safety) (zstVal : MirSemantics.Value)
    (c : CapturedMir) (mode : ClosureEnvMode) (m : Machine M) (fnNm : Gen.FnName) (addr : Nat)
    (prov : Option (Gen.Memory.Provenance M)) (fn : Gen.Function)
    (hCk : IsClosureCoercionTag ck) (hZst : zstVal = .unit ∨ zstVal = .aggregate 0 [])
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
      (callStack := mem.callStack) = .ok zstVal locals')
    (hSaf : reifyCoercionSafetyCompatible ck fnSaf = true)
    (hTy : operandTy decls layouts op = some { kind := .closure dp [], layoutIdx := li })
    (hLinked : findCallee? mem.callees dp = some c) (hDp : c.defPath = dp)
    (hShape : calleeOwnClosureShape? c = some (.nonCapturing mode)) (hTpc : c.typeParamCount = 0)
    (hConv : callConvEq c.fnAbi.conv .rust = true) (hArgc : c.argCount = length fnIns + 1)
    (hDecls : closureCalleeDeclsCompatible [] c.localDecls (length fnIns) fnIns fnOut = true)
    (hFresh : findFnPtrEntry? mem.fnPtrs dp [] (some (.fnPtr fnIns fnOut fnSaf .rust)) = none)
    (hNoB : lookupBorrow mem.borrows (nextFnPtrAllocId mem.fnPtrs) = none) (hAddr : addr < 2 ^ 64)
    (hMap : mapIndex m.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := prov })
    (hFn : fnFromPtrM m (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok fn)
    (hAr : fn.args.length = length fnIns) (hMrConv : fn.calling_convention = .Rust) :
    checkClosureCalleeSig mem.callees dp fnIns fnOut .rust = .ok ∧
    evalRvalue locals (.cast (.pointerCoercion ck) op { kind := .fnPtr fnIns fnOut fnSaf .rust, layoutIdx := 0 })
        mem decls layouts =
      .ok (.ptr (cfInternedPtr mem) 8) locals' (cfInternedMem mem dp (.fnPtr fnIns fnOut fnSaf .rust)) ∧
    ClosureFnPtrEntryRel (cfInternedMem mem dp (.fnPtr fnIns fnOut fnSaf .rust)) (cfInternedPtr mem) m fnNm addr
      prov c mode fn (length fnIns) ∧
    evalValueM m (.Constant (.FnPointer fnNm) thinRawPtrTy) =
      .ok ((.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none), thinRawPtrTy), m) := by
  have hSigOk : checkClosureCalleeSig mem.callees dp fnIns fnOut .rust = .ok := by
    rw [(checkClosureCalleeSig_callee_directed mem.callees dp fnIns fnOut c hLinked).2.2.2.1 mode hShape hTpc,
      hConv, hArgc, hDecls]
    have : Nat.beq (length fnIns + 1) (Nat.succ (length fnIns)) = true := Nat.beq_refl _
    rw [this]; rfl
  have hInt : internFnPtr mem dp [] (some (.fnPtr fnIns fnOut fnSaf .rust)) =
      (nextFnPtrAllocId mem.fnPtrs, cfInternedMem mem dp (.fnPtr fnIns fnOut fnSaf .rust)) := by
    unfold internFnPtr; simp only [hFresh]; rfl
  refine ⟨hSigOk, ?_, ?_, ?_⟩
  · rw [closureFnPointer_reify_callee_directed locals locals' op mem decls layouts ck dp li fnIns fnOut fnSaf
      .rust zstVal hCk hZst hOp rfl hSaf hTy, hSigOk, hInt]; rfl
  · refine ⟨⟨rfl, hNoB, hAddr, hMap⟩,
      ⟨{ allocId := nextFnPtrAllocId mem.fnPtrs, defPath := dp, typeArgs := [],
         fnSig := some (.fnPtr fnIns fnOut fnSaf .rust) }, ?_, hDp.symm, rfl⟩,
      ?_, hShape, hTpc, hArgc, hFn, hAr, hMrConv⟩
    · show lookupFnPtr (_ :: mem.fnPtrs) (nextFnPtrAllocId mem.fnPtrs) = _
      simp only [lookupFnPtr, Nat.beq_refl]
    · rw [hDp]; exact hLinked
  · unfold evalValueM evalConstantM
    simp only [hMap, bind, Except.bind, pure, Except.pure]

/-- **Universal call-ABI arity correspondence under `ClosureFnPtrEntryRel`.**
For related closure pointers: the Trusted body has exactly one parameter more
than the MiniRust function (the environment `_1`); an indirect Trusted call
with `n` arguments is gated by `checkClosureTargetCompatible` (never by the
non-closure `checkFnPtrTargetCompatible`) and enters with the environment
prepended; an indirect Trusted call with `n + 1` arguments (a forged pointer
passing the environment explicitly) is rejected; and MiniRust resolves the
pointer to the arity-`n` function. -/
theorem closureFnPtrEntryRel_call_arity {M : Type} [Gen.Memory M] [MemoryOps M] {mem : MirSemantics.Memory}
    {p : ProvenancePtr} {m : Machine M} {fnNm : Gen.FnName} {addr : Nat}
    {prov : Option (Gen.Memory.Provenance M)} {c : CapturedMir} {mode : ClosureEnvMode} {fn : Gen.Function}
    {n : Nat} (h : ClosureFnPtrEntryRel mem p m fnNm addr prov c mode fn n) :
    c.argCount = fn.args.length + 1 ∧
    (∀ target, target.isIndirect = true →
      checkCalleeTargetCompatible target c n = checkClosureTargetCompatible target c n ∧
      (∀ argVals, calleeEntryArgs target c argVals =
        synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) ∧
      checkCalleeTargetCompatible target c (n + 1) = false) ∧
    (∀ target, target.isIndirect = true → target.fnSig = none →
      checkCalleeTargetCompatible target c n = callConvEq c.fnAbi.conv .rust) ∧
    fnFromPtrM m (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok fn ∧
    (∀ fnIns fnOut, checkClosureCalleeSig mem.callees c.defPath fnIns fnOut .rust ≠ .unsupported) := by
  refine ⟨by rw [h.mrArity]; exact h.trustedArity, ?_, ?_, h.mrResolve, fun fnIns fnOut => ?_⟩
  · intro target hI
    refine ⟨by simp only [checkCalleeTargetCompatible, hI, h.shape], ?_, ?_⟩
    · intro argVals; simp only [calleeEntryArgs, hI, h.shape]
    · have hb : Nat.beq c.argCount (Nat.succ (n + 1)) = false := by
        rw [h.trustedArity]; exact nat_beq_self_succ_false (n + 1)
      simp only [checkCalleeTargetCompatible, hI, h.shape, checkClosureTargetCompatible, hb, Bool.false_and,
        Bool.and_false]
  · intro target hI hS
    have hb : Nat.beq c.argCount (Nat.succ n) = true := by rw [h.trustedArity]; exact Nat.beq_refl _
    simp only [checkCalleeTargetCompatible, hI, h.shape, checkClosureTargetCompatible, hb, hS, Bool.and_true]
  · rw [(checkClosureCalleeSig_callee_directed mem.callees c.defPath fnIns fnOut c h.linked).2.2.2.1 mode
      h.shape h.nonGeneric]
    split <;> simp

/-- **Universal MiniRust call-ABI law (`Machine::create_frame`, `Mach` &
`MachTB`).** Once the callee's return and argument locals are allocated and the
return types are ABI-compatible, MiniRust's call:
* is UB when the caller passes a number of arguments different from the
  callee's arity (`"number of arguments does not agree"`) — in particular an
  `(N + 1)`-argument call of an `N`-argument closure function;
* otherwise proceeds to bind the `N` arguments (`initFrameArgsM`);
* is UB whenever the calling conventions differ. -/
theorem minirust_createFrameM_arity_law {M : Type} [Gen.Memory M] [MemoryOps M] (m : Machine M)
    (func : Gen.Function) (spa : StackPopAction M) (callerRetTy : Gen.Type)
    (callerArgs : List (Gen.Value M × Gen.Type)) (f1 f2 : StackFrame M) (cm1 cm2 : ConcurrentMemory M)
    (calleeRetTy : Gen.Type)
    (hSL : storageLiveM { func := func, locals := ⟨[]⟩, stack_pop_action := spa, next_block := func.start, next_stmt := 0, extra := MemoryOps.new_call } m.mem func.ret = .ok (f1, cm1))
    (hAA : allocFrameArgsM f1 cm1 func.args = .ok (f2, cm2))
    (hRet : mapIndex f2.func.locals f2.func.ret "func.locals[func.ret]" = .ok calleeRetTy)
    (hAbi : checkAbiCompatibility callerRetTy calleeRetTy = .ok true) :
    (func.args.length ≠ callerArgs.length →
      createFrameM m func spa func.calling_convention callerRetTy callerArgs =
        .error (.ub "call ABI violation: number of arguments does not agree")) ∧
    (func.args.length = callerArgs.length →
      createFrameM m func spa func.calling_convention callerRetTy callerArgs =
        (initFrameArgsM { m with mem := cm2 } f2 func.args callerArgs).map (fun m' => (f2, m'))) ∧
    (∀ conv, conv ≠ func.calling_convention →
      createFrameM m func spa conv callerRetTy callerArgs =
        .error (.ub "call ABI violation: calling conventions are not the same")) := by
  refine ⟨fun hne => ?_, fun heq => ?_, fun conv hconv => ?_⟩
  · unfold createFrameM
    simp only [hSL, hAA, hRet, hAbi, bind, Except.bind, ub, ne_eq, not_true_eq_false,
      ↓reduceIte, Bool.not_true, Bool.false_eq_true, hne, not_false_eq_true]
  · unfold createFrameM
    simp only [hSL, hAA, hRet, hAbi, bind, Except.bind, pure, Except.pure, ne_eq, not_true_eq_false,
      ↓reduceIte, Bool.not_true, Bool.false_eq_true, heq]
    cases initFrameArgsM { m with mem := cm2 } f2 func.args callerArgs <;> rfl
  · unfold createFrameM
    simp only [hSL, hAA, bind, Except.bind, ub, ne_eq, hconv, not_false_eq_true, ↓reduceIte]

/-- **Universal MiniRust return-type & argument-type ABI-mismatch law
(`Machine::create_frame` / `initFrameArgsM`, `Mach` & `MachTB`).** Completes
`minirust_createFrameM_arity_law` across all four ABI checks of
`spec/lang/step/terminators.md`:
* an ABI-incompatible return type (`checkAbiCompatibility callerRetTy calleeRetTy = .ok false`)
  faults with `"call ABI violation: return types are not compatible"`;
* an ABI-incompatible first argument (`checkAbiCompatibility callerArgTy calleeArgTy = .ok false`)
  causes `initFrameArgsM` and `createFrameM` to fault with
  `"call ABI violation: argument types are not compatible"`. -/
theorem minirust_createFrameM_abi_mismatch_law {M : Type} [Gen.Memory M] [MemoryOps M] (m : Machine M)
    (func : Gen.Function) (spa : StackPopAction M) (callerRetTy : Gen.Type)
    (callerArgs : List (Gen.Value M × Gen.Type)) (f1 f2 : StackFrame M) (cm1 cm2 : ConcurrentMemory M)
    (calleeRetTy : Gen.Type)
    (hSL : storageLiveM { func := func, locals := ⟨[]⟩, stack_pop_action := spa, next_block := func.start, next_stmt := 0, extra := MemoryOps.new_call } m.mem func.ret = .ok (f1, cm1))
    (hAA : allocFrameArgsM f1 cm1 func.args = .ok (f2, cm2))
    (hRet : mapIndex f2.func.locals f2.func.ret "func.locals[func.ret]" = .ok calleeRetTy) :
    (checkAbiCompatibility callerRetTy calleeRetTy = .ok false →
      createFrameM m func spa func.calling_convention callerRetTy callerArgs =
        .error (.ub "call ABI violation: return types are not compatible")) ∧
    (∀ argLoc restLocs argVal callerArgTy restArgs calleeArgTy,
      func.args = argLoc :: restLocs →
      callerArgs = (argVal, callerArgTy) :: restArgs →
      restLocs.length = restArgs.length →
      checkAbiCompatibility callerRetTy calleeRetTy = .ok true →
      mapIndex f2.func.locals argLoc "func.locals[callee_local]" = .ok calleeArgTy →
      checkAbiCompatibility callerArgTy calleeArgTy = .ok false →
      initFrameArgsM { m with mem := cm2 } f2 func.args callerArgs =
        .error (.ub "call ABI violation: argument types are not compatible") ∧
      createFrameM m func spa func.calling_convention callerRetTy callerArgs =
        .error (.ub "call ABI violation: argument types are not compatible")) := by
  refine ⟨fun hBadRet => ?_, fun argLoc restLocs argVal callerArgTy restArgs calleeArgTy hArgs hCArgs hLen hOkRet hArgTy hBadArg => ?_⟩
  · unfold createFrameM
    simp only [hSL, hAA, hRet, hBadRet, bind, Except.bind, ub, ne_eq, not_true_eq_false,
      ↓reduceIte, Bool.not_false]
  · have hInit : initFrameArgsM { m with mem := cm2 } f2 func.args callerArgs =
        .error (.ub "call ABI violation: argument types are not compatible") := by
      rw [hArgs, hCArgs]
      unfold initFrameArgsM
      simp only [hArgTy, hBadArg, bind, Except.bind, ub, Bool.not_false, ↓reduceIte]
    refine ⟨hInit, ?_⟩
    have hEqLen : func.args.length = callerArgs.length := by
      rw [hArgs, hCArgs]; simp only [List.length_cons, hLen]
    have hMain := (minirust_createFrameM_arity_law m func spa callerRetTy callerArgs f1 f2 cm1 cm2
      calleeRetTy hSL hAA hRet hOkRet).2.1 hEqLen
    rw [hMain, hInit]
    rfl

/-- Translate a Trusted function-pointer ABI type `RigidTy` to its MiniRust `Gen.Type`
via `MiniRustSpec.Correspondence.translateTy` (with function pointers mapped to
`thinRawPtrTy`). -/
def cfTranslateAbiTy (rk : RigidTy) : Option Gen.Type :=
  match rk with
  | .fnPtr .. => some thinRawPtrTy
  | _ => translateTy ⟨64, true, []⟩ { kind := rk, layoutIdx := 0 }

/-- Pairwise argument-type correspondence between Trusted closure parameters
`fnIns` (after skipping `_1`) and MiniRust function arguments `fn.args`. -/
def cfArgsSigRel (fn : Gen.Function) : List RigidTy → List LocalName → Prop
  | [], [] => True
  | rk :: rks, argLoc :: locs =>
    (∃ mrArg, cfTranslateAbiTy rk = some mrArg ∧
      mapIndex fn.locals argLoc "func.locals[callee_local]" = .ok mrArg) ∧
    cfArgsSigRel fn rks locs
  | _, _ => False

/-- **Typed signature correspondence between a Trusted closure body `c` and its
MiniRust image `fn`**: ties BOTH the return type (`_0` vs `fn.locals[fn.ret]`)
AND every user-visible argument type (`_2 .. _{n+1}` after skipping the closure
environment `_1`, vs `fn.locals[fn.args[i]]`) through `cfTranslateAbiTy`. -/
structure ClosureFnSigRel (c : CapturedMir) (fn : Gen.Function) (fnIns : List RigidTy) (fnOut : RigidTy)
    (mrRetTy : Gen.Type) : Prop where
  decls : ∃ retDecl envDecl paramDecls,
    c.localDecls = retDecl :: envDecl :: paramDecls ∧
    retDecl.ty.kind = fnOut ∧
    Nat.ble (length fnIns) (length paramDecls) = true ∧
    calleeParamTysMatch [] fnIns paramDecls = true
  retTranslate : cfTranslateAbiTy fnOut = some mrRetTy
  mrRetLookup : mapIndex fn.locals fn.ret "func.locals[func.ret]" = .ok mrRetTy
  argsRel : cfArgsSigRel fn fnIns fn.args

/-- **Universal two-sided typed-signature ABI-mismatch correspondence (`Mach` &
`MachTB`)**: whenever a Trusted closure pointer and MiniRust function are linked
by `ClosureFnPtrEntryRel` AND `ClosureFnSigRel c fn fnIns fnOut mrRetTy`:
1. the MiniRust function has arity `fnIns.length` and the Trusted closure body
   has `argCount = fnIns.length + 1`;
2. **return-type transmutation UB lockstep**: for ANY transmuted caller return
   type `badOut` (failing `rigidTyMatchesCalleeDecl [] 8 badOut fnOut`) paired
   with an ABI-incompatible MiniRust return type `badMrRet`, BOTH Trusted
   (`evalTerminator = .fail .ub`) AND MiniRust (`createFrameM = .error (.ub
   "call ABI violation: return types are not compatible")`) fault with UB;
3. **argument-type transmutation UB lockstep**: for ANY non-empty signature
   `fnIns = in0 :: restIns` and transmuted caller argument list `badIn0 :: restBad`
   (failing `calleeParamTysMatch [] (badIn0 :: restBad) paramDecls`) paired
   with an ABI-incompatible MiniRust first argument `badMrArg`, BOTH Trusted
   (`evalTerminator = .fail .ub`) AND MiniRust (`createFrameM = .error (.ub
   "call ABI violation: argument types are not compatible")`) fault with UB. -/
theorem closure_typed_sig_call_correspondence_M {M : Type} [Gen.Memory M] [MemoryOps M]
    {p : ProvenancePtr} {m : Machine M} {fnNm : Gen.FnName} {addr : Nat}
    {prov : Option (Gen.Memory.Provenance M)} {c : CapturedMir} {mode : ClosureEnvMode} {fn : Gen.Function}
    {fnIns : List RigidTy} {fnOut : RigidTy} {mrRetTy : Gen.Type}
    (s : MachineState) (callerBody : CapturedMir) (func : MirAst.Operand) (argOps : List MirAst.Operand)
    (dest : MirAst.Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction) (span : String)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value)
    (hRel : ClosureFnPtrEntryRel s.memory p m fnNm addr prov c mode fn fnIns.length)
    (hSig : ClosureFnSigRel c fn fnIns fnOut mrRetTy)
    (hNotDir : extractCalleeDefPath? func = none)
    (hFunc : evalOperandWithBodyCast s.frame.locals func s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack =
      .ok (.ptr p 8) localsAfterFunc)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hLook : lookupCallee s.memory.callees callerBody.layouts c.defPath [] s.memory.traitImpls = some c)
    (spa : StackPopAction M) (f1 f2 : StackFrame M) (cm1 cm2 : ConcurrentMemory M)
    (hSL : storageLiveM { func := fn, locals := ⟨[]⟩, stack_pop_action := spa, next_block := fn.start, next_stmt := 0, extra := MemoryOps.new_call } m.mem fn.ret = .ok (f1, cm1))
    (hAA : allocFrameArgsM f1 cm1 fn.args = .ok (f2, cm2))
    (hF2Func : f2.func = fn) :
    (fn.args.length = fnIns.length ∧ c.argCount = fnIns.length + 1) ∧
    (∀ e badIns badOut badSaf badMrRet callerArgs,
      lookupFnPtr s.memory.fnPtrs p.allocId = some e →
      e.fnSig = some (.fnPtr badIns badOut badSaf .rust) →
      fnEntryCompatibleWithCallSite e (length argOps) (operandTy callerBody.localDecls callerBody.layouts func) = true →
      rigidTyMatchesCalleeDecl [] 8 badOut fnOut = false →
      checkAbiCompatibility badMrRet mrRetTy = .ok false →
      evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
        MirStepNode.fail .ub ∧
      createFrameM m fn spa .Rust badMrRet callerArgs =
        .error (.ub "call ABI violation: return types are not compatible")) ∧
    (∀ in0 restIns argLoc0 restLocs e badIn0 restBad badOut badSaf argVal badMrArg restArgs mrArg0,
      fnIns = in0 :: restIns →
      fn.args = argLoc0 :: restLocs →
      mapIndex fn.locals argLoc0 "func.locals[callee_local]" = .ok mrArg0 →
      lookupFnPtr s.memory.fnPtrs p.allocId = some e →
      e.fnSig = some (.fnPtr (badIn0 :: restBad) badOut badSaf .rust) →
      fnEntryCompatibleWithCallSite e (length argOps) (operandTy callerBody.localDecls callerBody.layouts func) = true →
      (∀ retDecl envDecl paramDecls, c.localDecls = retDecl :: envDecl :: paramDecls →
        calleeParamTysMatch [] (badIn0 :: restBad) paramDecls = false) →
      restLocs.length = restArgs.length →
      checkAbiCompatibility mrRetTy mrRetTy = .ok true →
      checkAbiCompatibility badMrArg mrArg0 = .ok false →
      evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
        MirStepNode.fail .ub ∧
      createFrameM m fn spa .Rust mrRetTy ((argVal, badMrArg) :: restArgs) =
        .error (.ub "call ABI violation: argument types are not compatible")) := by
  obtain ⟨e0, hEntry0, hDp0, hTargs0⟩ := hRel.fnEntry
  obtain ⟨hOff, hNoB, _, _⟩ := hRel.entry
  obtain ⟨retDecl, envDecl, paramDecls, hDeclsEq, hRetKindEq, _, _⟩ := hSig.decls
  have hRetF2 : mapIndex f2.func.locals f2.func.ret "func.locals[func.ret]" = .ok mrRetTy := by
    rw [hF2Func]; exact hSig.mrRetLookup
  refine ⟨⟨hRel.mrArity, hRel.trustedArity⟩, ?_, ?_⟩
  · intro e badIns badOut badSaf badMrRet callerArgs hE hESig hCompat hBadOut hBadMrRet
    have hEqE : e = e0 := Option.some.inj (hE.symm.trans hEntry0)
    subst hEqE
    have hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true } localsAfterFunc := by
      unfold resolveCallTarget
      simp only [hNotDir, hFunc, hOff, hNoB, hE, hCompat, hDp0, hTargs0, Nat.beq_refl, Bool.and_self]
    have hDeclFalse : closureCalleeDeclsCompatible [] c.localDecls (length argVals) badIns badOut = false := by
      unfold closureCalleeDeclsCompatible
      rw [hDeclsEq]
      dsimp only
      unfold calleeLocalDeclsCompatible
      dsimp only
      rw [hRetKindEq, hBadOut]
      simp only [Bool.false_and, Bool.and_false]
    have hTargetFalse : checkCalleeTargetCompatible
        { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true } c (length argVals) = false := by
      simp only [checkCalleeTargetCompatible, hRel.shape, checkClosureTargetCompatible, hESig,
        hDeclFalse, Bool.and_false]
    refine ⟨?_, ?_⟩
    · simp only [MirSemantics.evalTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hTargetFalse]
    · rw [← hRel.mrConv]
      exact (minirust_createFrameM_abi_mismatch_law m fn spa badMrRet callerArgs f1 f2 cm1 cm2
        mrRetTy hSL hAA hRetF2).1 hBadMrRet
  · intro in0 restIns argLoc0 restLocs e badIn0 restBad badOut badSaf argVal badMrArg restArgs mrArg0
      _ hFnArgs hArg0Ty hE hESig hCompat hBadIn hRestLen hOkRet hBadMrArg
    have hEqE : e = e0 := Option.some.inj (hE.symm.trans hEntry0)
    subst hEqE
    have hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true } localsAfterFunc := by
      unfold resolveCallTarget
      simp only [hNotDir, hFunc, hOff, hNoB, hE, hCompat, hDp0, hTargs0, Nat.beq_refl, Bool.and_self]
    have hDeclFalse : closureCalleeDeclsCompatible [] c.localDecls (length argVals) (badIn0 :: restBad) badOut = false := by
      unfold closureCalleeDeclsCompatible
      rw [hDeclsEq]
      dsimp only
      unfold calleeLocalDeclsCompatible
      dsimp only
      rw [hBadIn retDecl envDecl paramDecls hDeclsEq]
      simp only [Bool.and_false]
    have hTargetFalse : checkCalleeTargetCompatible
        { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true } c (length argVals) = false := by
      simp only [checkCalleeTargetCompatible, hRel.shape, checkClosureTargetCompatible, hESig,
        hDeclFalse, Bool.and_false]
    have hArg0F2 : mapIndex f2.func.locals argLoc0 "func.locals[callee_local]" = .ok mrArg0 := by
      rw [hF2Func]; exact hArg0Ty
    refine ⟨?_, ?_⟩
    · simp only [MirSemantics.evalTerminator, bodyLocalDeclsOf, hRes, hArgs, hLook, hTargetFalse]
    · rw [← hRel.mrConv]
      exact ((minirust_createFrameM_abi_mismatch_law m fn spa mrRetTy ((argVal, badMrArg) :: restArgs)
        f1 f2 cm1 cm2 mrRetTy hSL hAA hRetF2).2 argLoc0 restLocs argVal badMrArg restArgs mrArg0
        hFnArgs rfl hRestLen hOkRet hArg0F2 hBadMrArg).2

/-- **Universal MiniRust pointer identity (`raw_c == raw_d`, `Mach` & `MachTB`).**
`BinOp::Rel(Eq)` on two thin pointers with the same address is `true`
regardless of provenance, for any pointer type. -/
theorem minirust_ptr_rel_eq_same_addr_M {M : Type} [Gen.Memory M] (addr : Nat)
    (prov1 prov2 : Option (Gen.Memory.Provenance M)) (ty1 : PtrType) (ty2 : Gen.Type) :
    evalBinOpM (M := M) (.Rel .Eq)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := prov1 } none), .Ptr ty1)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := prov2 } none), ty2) =
      .ok (.Bool true, .Bool) := by
  unfold evalBinOpM
  simp [comparePtrM, ThinPointer.widen, intCmp, evalRelOpM, bind, Except.bind, pure, Except.pure]

/-- **Universal `MachTB.wfLive` preservation of the MiniRust indirect call and
return steps.** Every successful `Terminator::Call` step (in particular the
`N`-argument indirect closure call) and every successful `Terminator::Return`
of a well-formed `MachTB` yields a well-formed `MachTB`; so does any successful
`stepTB` / `stepsTB` run. -/
theorem minirust_closure_call_return_tb_wfLive {m m' : MachTB} (hwf : MachTB.wfLive m) :
    (∀ callee conv args ret next unwindBb,
      evalTerminatorM m (.Call callee conv args ret next unwindBb) = .ok m' → MachTB.wfLive m') ∧
    (evalTerminatorM m .Return = .ok m' → MachTB.wfLive m') ∧
    (Interp.stepTB m = .ok m' → MachTB.wfLive m') ∧
    (∀ n, Interp.stepsTB n m = .ok m' → MachTB.wfLive m') :=
  ⟨fun _ _ _ _ _ _ h => evalTerminatorM_tb_wfLive hwf h, fun h => evalTerminatorM_tb_wfLive hwf h,
   fun h => stepTB_wfLive hwf h, fun _ h => stepsTB_wfLive hwf h⟩

/-- **Universal coercion → widening → pointer-identity pipeline for arbitrary
signatures `fn(fnIns) -> fnOut`, covering BOTH `ClosureFnPointer(Safe)` +
`UnsafeFnPointer` + `FnPtrToPtr` AND direct `ClosureFnPointer(Unsafe)` +
`FnPtrToPtr` (`Mach` & `MachTB`, preserving `MachTB.wfLive`).**
For any non-capturing closure signature `fn(fnIns) -> fnOut` (with reflexive
fuel-bounded equality `rigidTyListEq fnIns fnIns = true` and `rigidTyEq fnOut fnOut = true`):
* under a safe coercion tag (`ClosureFnPointer(Safe)` / `"ClosureFnPointer"`),
  reification establishes `ClosureFnPtrEntryRel` on `Mach` and `MachTB`,
  `UnsafeFnPointer` widening preserves the exact pointer `p`, and `FnPtrToPtr`
  of both the safe and widened unsafe pointers produces `.ptr p 8` (pointer
  identity `raw_c == raw_d`), matching MiniRust `Constant::FnPointer`,
  `Transmute`, and `BinOp::Rel(Eq)` (`true`) on both `Mach` and `MachTB`;
* under an unsafe coercion tag (`ClosureFnPointer(Unsafe)` / `"ClosureFnPointer"`),
  direct reification to `unsafe fn(fnIns) -> fnOut` establishes
  `ClosureFnPtrEntryRel` on `Mach` and `MachTB` and `FnPtrToPtr` preserves
  `.ptr p 8`, matching MiniRust on both `Mach` and `MachTB`. -/
theorem closure_coercion_widening_identity_general_mach_and_tb
    (locals locals1 locals2 locals3 locals4 : List LocalSlot)
    (opReify opUnsafe opRawC opRawD : MirAst.Operand) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (ck : String) (dp : DefPath) (li : Nat)
    (fnIns : List RigidTy) (fnOut : RigidTy) (fnSaf : Safety)
    (zstVal : MirSemantics.Value) (c : CapturedMir) (mode : ClosureEnvMode) (fnNm : Gen.FnName) (addr : Nat)
    (hAddr : addr < 2 ^ 64) (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Mach)
    (mTB : MachTB) (fnBM fnTB : Gen.Function)
    (hCk : IsClosureCoercionTag ck) (hZst : zstVal = .unit ∨ zstVal = .aggregate 0 [])
    (hSaf : reifyCoercionSafetyCompatible ck fnSaf = true)
    (hInRefl : rigidTyListEq fnIns fnIns = true) (hOutRefl : rigidTyEq fnOut fnOut = true)
    (hTy : operandTy decls layouts opReify = some { kind := .closure dp [], layoutIdx := li })
    (hLinked : findCallee? mem.callees dp = some c) (hDp : c.defPath = dp)
    (hShape : calleeOwnClosureShape? c = some (.nonCapturing mode)) (hTpc : c.typeParamCount = 0)
    (hConv : callConvEq c.fnAbi.conv .rust = true) (hArgc : c.argCount = length fnIns + 1)
    (hDecls : closureCalleeDeclsCompatible [] c.localDecls (length fnIns) fnIns fnOut = true)
    (hFresh : findFnPtrEntry? mem.fnPtrs dp [] (some (.fnPtr fnIns fnOut fnSaf .rust)) = none)
    (hNoB : lookupBorrow mem.borrows (nextFnPtrAllocId mem.fnPtrs) = none)
    (hMapBM : mapIndex mBM.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := provBM })
    (hMapTB : mapIndex mTB.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := provTB })
    (hFnBM : fnFromPtrM mBM (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)) = .ok fnBM)
    (hFnTB : fnFromPtrM mTB (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none)) = .ok fnTB)
    (hArBM : fnBM.args.length = length fnIns) (hArTB : fnTB.args.length = length fnIns)
    (hConvBM : fnBM.calling_convention = .Rust) (hConvTB : fnTB.calling_convention = .Rust)
    (hOp1 : evalOperand locals opReify mem.borrows mem.globals layouts mem.callerLocals
      (callStack := mem.callStack) = .ok zstVal locals1) :
    let sigKind : RigidTy := .fnPtr fnIns fnOut fnSaf .rust
    let sigTy : MirAst.Ty := { kind := sigKind, layoutIdx := 0 }
    let unsafeTy : MirAst.Ty := { kind := .fnPtr fnIns fnOut .unsafe_ .rust, layoutIdx := 0 }
    let mem1 := cfInternedMem mem dp sigKind
    let p := cfInternedPtr mem
    evalRvalue locals (.cast (.pointerCoercion ck) opReify sigTy) mem decls layouts =
      .ok (.ptr p 8) locals1 mem1 ∧
    ClosureFnPtrEntryRel mem1 p mBM fnNm addr provBM c mode fnBM (length fnIns) ∧
    ClosureFnPtrEntryRel mem1 p mTB fnNm addr provTB c mode fnTB (length fnIns) ∧
    (fnSaf = .safe →
      evalOperand locals1 opUnsafe mem1.borrows mem1.globals layouts mem1.callerLocals decls mem1.callStack =
        .ok (.ptr p 8) locals2 →
      operandTy decls layouts opUnsafe = some sigTy →
      evalRvalue locals1 (.cast (.pointerCoercion "UnsafeFnPointer") opUnsafe unsafeTy) mem1 decls layouts =
        .ok (.ptr p 8) locals2 mem1) ∧
    (evalOperand locals2 opRawC mem1.borrows mem1.globals layouts mem1.callerLocals decls mem1.callStack =
        .ok (.ptr p 8) locals3 →
      operandTy decls layouts opRawC = some sigTy →
      evalRvalue locals2 (.cast .fnPtrToPtr opRawC rawConstUnitMirTy) mem1 decls layouts =
        .ok (.ptr p 8) locals3 mem1) ∧
    (evalOperand locals3 opRawD mem1.borrows mem1.globals layouts mem1.callerLocals decls mem1.callStack =
        .ok (.ptr p 8) locals4 →
      operandTy decls layouts opRawD = some unsafeTy →
      evalRvalue locals3 (.cast .fnPtrToPtr opRawD rawConstUnitMirTy) mem1 decls layouts =
        .ok (.ptr p 8) locals4 mem1) ∧
    evalValueM mBM (.Constant (.FnPointer fnNm) thinRawPtrTy) =
      .ok ((.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy), mBM) ∧
    evalValueM mTB (.Constant (.FnPointer fnNm) thinRawPtrTy) =
      .ok ((.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy), mTB) ∧
    evalCastOp (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) (some mBM) =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) (some mTB) =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) ∧
    evalBinOpM (M := BM) (.Rel .Eq)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) =
      .ok (.Bool true, .Bool) ∧
    evalBinOpM (M := TBM) (.Rel .Eq)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) =
      .ok (.Bool true, .Bool) := by
  have hBM := closure_reify_establishes_entryRel_M (M := BM) locals locals1 opReify mem decls layouts ck dp li
    fnIns fnOut fnSaf zstVal c mode mBM fnNm addr provBM fnBM hCk hZst hOp1 hSaf hTy hLinked hDp
    hShape hTpc hConv hArgc hDecls hFresh hNoB hAddr hMapBM hFnBM hArBM hConvBM
  have hTB := closure_reify_establishes_entryRel_M (M := TBM) locals locals1 opReify mem decls layouts ck dp li
    fnIns fnOut fnSaf zstVal c mode mTB fnNm addr provTB fnTB hCk hZst hOp1 hSaf hTy hLinked hDp
    hShape hTpc hConv hArgc hDecls hFresh hNoB hAddr hMapTB hFnTB hArTB hConvTB
  have hRelBM := hBM.2.2.1.entry
  have hRelTB := hTB.2.2.1.entry
  refine ⟨hBM.2.1, hBM.2.2.1, hTB.2.2.1, ?_, ?_, ?_, hBM.2.2.2, hTB.2.2.2,
    evalCastOp_transmute_thinRawPtr_id addr hAddr provBM (some mBM),
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB (some mTB),
    minirust_ptr_rel_eq_same_addr_M (M := BM) addr provBM provBM _ _,
    minirust_ptr_rel_eq_same_addr_M (M := TBM) addr provTB provTB _ _⟩
  · intro hSafe hOp2 hTy2
    subst hSafe
    show evalUnsafeFnPointer locals1 opUnsafe { kind := .fnPtr fnIns fnOut .unsafe_ .rust, layoutIdx := 0 }
      (cfInternedMem mem dp (.fnPtr fnIns fnOut .safe .rust)) decls layouts =
      .ok (.ptr (cfInternedPtr mem) 8) locals2 (cfInternedMem mem dp (.fnPtr fnIns fnOut .safe .rust))
    unfold evalUnsafeFnPointer
    rw [hOp2, hTy2]
    have hTag : lookupBorrow mem.borrows (cfInternedPtr mem).tag = none := hRelBM.2.1
    simp only [cfInternedMem]
    rw [hTag]
    simp only [cfInternedPtr, callConvEq, hInRefl, hOutRefl, Nat.beq_refl, lookupFnPtr, Bool.and_self]
  · intro hOp3 hTy3
    exact (fnPtrToPtr_lockstep_mach_and_tb locals2 locals3 opRawC rawConstUnitMirTy
      (cfInternedMem mem dp (.fnPtr fnIns fnOut fnSaf .rust)) decls layouts (cfInternedPtr mem) fnNm addr provBM provTB
      mBM mTB hRelBM hRelTB hOp3 rfl (by simp [hTy3, callConvEq])
      (by simp [cfInternedMem, cfInternedPtr, lookupFnPtr, Nat.beq_refl, callConvEq])).1
  · intro hOp4 hTy4
    exact (fnPtrToPtr_lockstep_mach_and_tb locals3 locals4 opRawD rawConstUnitMirTy
      (cfInternedMem mem dp (.fnPtr fnIns fnOut fnSaf .rust)) decls layouts (cfInternedPtr mem) fnNm addr provBM provTB
      mBM mTB hRelBM hRelTB hOp4 rfl (by simp [hTy4, callConvEq])
      (by simp [cfInternedMem, cfInternedPtr, lookupFnPtr, Nat.beq_refl, callConvEq])).1

/-- **Universal coercion → widening → pointer-identity pipeline for `fn(u32) -> u32`
closure pointers (`Mach` & `MachTB`)** — specialization of
`closure_coercion_widening_identity_general_mach_and_tb`. -/
theorem closure_coercion_widening_identity_mach_and_tb (locals locals1 locals2 locals3 locals4 : List LocalSlot)
    (opReify opUnsafe opRawC opRawD : MirAst.Operand) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (ck : String) (dp : DefPath) (li : Nat)
    (zstVal : MirSemantics.Value) (c : CapturedMir) (mode : ClosureEnvMode) (fnNm : Gen.FnName) (addr : Nat)
    (hAddr : addr < 2 ^ 64) (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Mach)
    (mTB : MachTB) (fnBM fnTB : Gen.Function)
    (hCk : IsClosureCoercionTag ck) (hZst : zstVal = .unit ∨ zstVal = .aggregate 0 [])
    (hSaf : reifyCoercionSafetyCompatible ck .safe = true)
    (hTy : operandTy decls layouts opReify = some { kind := .closure dp [], layoutIdx := li })
    (hLinked : findCallee? mem.callees dp = some c) (hDp : c.defPath = dp)
    (hShape : calleeOwnClosureShape? c = some (.nonCapturing mode)) (hTpc : c.typeParamCount = 0)
    (hConv : callConvEq c.fnAbi.conv .rust = true) (hArgc : c.argCount = 2)
    (hDecls : closureCalleeDeclsCompatible [] c.localDecls 1 [.uint .u32] (.uint .u32) = true)
    (hFresh : findFnPtrEntry? mem.fnPtrs dp [] (some fnPtrSafeU32MirTy.kind) = none)
    (hNoB : lookupBorrow mem.borrows (nextFnPtrAllocId mem.fnPtrs) = none)
    (hMapBM : mapIndex mBM.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := provBM })
    (hMapTB : mapIndex mTB.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := provTB })
    (hFnBM : fnFromPtrM mBM (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)) = .ok fnBM)
    (hFnTB : fnFromPtrM mTB (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none)) = .ok fnTB)
    (hArBM : fnBM.args.length = 1) (hArTB : fnTB.args.length = 1)
    (hConvBM : fnBM.calling_convention = .Rust) (hConvTB : fnTB.calling_convention = .Rust)
    (hOp1 : evalOperand locals opReify mem.borrows mem.globals layouts mem.callerLocals
      (callStack := mem.callStack) = .ok zstVal locals1) :
    evalRvalue locals (.cast (.pointerCoercion ck) opReify fnPtrSafeU32MirTy) mem decls layouts =
      .ok (.ptr (cfInternedPtr mem) 8) locals1 (cfInternedMem mem dp fnPtrSafeU32MirTy.kind) ∧
    ClosureFnPtrEntryRel (cfInternedMem mem dp fnPtrSafeU32MirTy.kind) (cfInternedPtr mem) mBM fnNm addr provBM
      c mode fnBM 1 ∧
    ClosureFnPtrEntryRel (cfInternedMem mem dp fnPtrSafeU32MirTy.kind) (cfInternedPtr mem) mTB fnNm addr provTB
      c mode fnTB 1 ∧
    (evalOperand locals1 opUnsafe (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).borrows
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).globals layouts
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).callerLocals decls
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).callStack = .ok (.ptr (cfInternedPtr mem) 8) locals2 →
      operandTy decls layouts opUnsafe = some fnPtrSafeU32MirTy →
      evalRvalue locals1 (.cast (.pointerCoercion "UnsafeFnPointer") opUnsafe fnPtrUnsafeU32MirTy)
          (cfInternedMem mem dp fnPtrSafeU32MirTy.kind) decls layouts =
        .ok (.ptr (cfInternedPtr mem) 8) locals2 (cfInternedMem mem dp fnPtrSafeU32MirTy.kind)) ∧
    (evalOperand locals2 opRawC (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).borrows
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).globals layouts
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).callerLocals decls
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).callStack = .ok (.ptr (cfInternedPtr mem) 8) locals3 →
      operandTy decls layouts opRawC = some fnPtrSafeU32MirTy →
      evalRvalue locals2 (.cast .fnPtrToPtr opRawC rawConstUnitMirTy)
          (cfInternedMem mem dp fnPtrSafeU32MirTy.kind) decls layouts =
        .ok (.ptr (cfInternedPtr mem) 8) locals3 (cfInternedMem mem dp fnPtrSafeU32MirTy.kind)) ∧
    (evalOperand locals3 opRawD (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).borrows
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).globals layouts
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).callerLocals decls
        (cfInternedMem mem dp fnPtrSafeU32MirTy.kind).callStack = .ok (.ptr (cfInternedPtr mem) 8) locals4 →
      operandTy decls layouts opRawD = some fnPtrUnsafeU32MirTy →
      evalRvalue locals3 (.cast .fnPtrToPtr opRawD rawConstUnitMirTy)
          (cfInternedMem mem dp fnPtrSafeU32MirTy.kind) decls layouts =
        .ok (.ptr (cfInternedPtr mem) 8) locals4 (cfInternedMem mem dp fnPtrSafeU32MirTy.kind)) ∧
    evalValueM mBM (.Constant (.FnPointer fnNm) thinRawPtrTy) =
      .ok ((.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy), mBM) ∧
    evalValueM mTB (.Constant (.FnPointer fnNm) thinRawPtrTy) =
      .ok ((.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy), mTB) ∧
    evalCastOp (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) (some mBM) =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) (some mTB) =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) ∧
    evalBinOpM (M := BM) (.Rel .Eq)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) =
      .ok (.Bool true, .Bool) ∧
    evalBinOpM (M := TBM) (.Rel .Eq)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) =
      .ok (.Bool true, .Bool) := by
  have hG := closure_coercion_widening_identity_general_mach_and_tb locals locals1 locals2 locals3 locals4
    opReify opUnsafe opRawC opRawD mem decls layouts ck dp li [.uint .u32] (.uint .u32) .safe zstVal c mode fnNm
    addr hAddr provBM provTB mBM mTB fnBM fnTB hCk hZst hSaf rfl rfl hTy hLinked hDp hShape hTpc hConv hArgc
    hDecls hFresh hNoB hMapBM hMapTB hFnBM hFnTB hArBM hArTB hConvBM hConvTB hOp1
  exact ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1 rfl, hG.2.2.2.2⟩

/-- **Universal classification of a closure receiver by its captured upvars.**
For the body's own closure path `p`, the three receiver forms `&{closure}`,
`&mut {closure}`, and `{closure}` classify as `.nonCapturing` (`Fn`, `FnMut`,
`FnOnce`) exactly when the upvar list is empty, and as `.capturing` for EVERY
non-empty upvar list (zero-sized upvars such as `()` included); a receiver of
a different closure path is not a closure receiver at all. -/
theorem classifyOwnClosureEnvTy_by_upvars (p : DefPath) (u : RigidTy) (us : List RigidTy) :
    classifyOwnClosureEnvTy? p (.ref .not (.closure p [])) = some (.nonCapturing .sharedRef) ∧
    classifyOwnClosureEnvTy? p (.ref .mut (.closure p [])) = some (.nonCapturing .mutRef) ∧
    classifyOwnClosureEnvTy? p (.closure p []) = some (.nonCapturing .byValue) ∧
    classifyOwnClosureEnvTy? p (.ref .not (.closure p (u :: us))) = some .capturing ∧
    classifyOwnClosureEnvTy? p (.ref .mut (.closure p (u :: us))) = some .capturing ∧
    classifyOwnClosureEnvTy? p (.closure p (u :: us)) = some .capturing ∧
    (∀ q ups, stringEq q p = false →
      classifyOwnClosureEnvTy? p (.ref .not (.closure q ups)) = none ∧
      classifyOwnClosureEnvTy? p (.ref .mut (.closure q ups)) = none ∧
      classifyOwnClosureEnvTy? p (.closure q ups) = none) := by
  have hp : stringEq p p = true := stringEq_eq_true.mpr rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (simp only [classifyOwnClosureEnvTy?, hp, closureShapeOfUpvars])
  intro q ups hq
  simp only [hq, and_self]

/-- **Universal coupled two-sided indirect closure call correspondence (`Mach` &
`MachTB`).** For a Trusted state `s` and MiniRust machine `m` whose function
pointers `p` (in `s.memory`) and `(addr, prov)` (in `m.fn_ptrs[fnNm]`) are
coupled by `ClosureFnPtrEntryRel s.memory p m fnNm addr prov c mode fn n`
(Trusted body `c` with `n + 1` parameters, MiniRust function `fn` of arity `n`),
when the Trusted callee operand `func` evaluates directly to `.ptr p 8` (so
`resolveCallTarget` resolves `p` through `hRel.fnEntry` and `hRel.entry`) and
MiniRust resolves `(addr, prov)` through `hRel.mrResolve` (`fnFromPtrM`):
* with `n` arguments and a compatible pointer signature, Trusted enters `c`
  with the synthesized environment prepended (`n + 1` entry arguments) while
  MiniRust's `fnFromPtrM` + `createFrameM` accepts the arity and proceeds to
  bind exactly the `n` caller arguments;
* with `n + 1` arguments (a forged pointer passing the environment
  explicitly), BOTH fault: Trusted with `.ub`, MiniRust with
  `"call ABI violation: number of arguments does not agree"`. -/
theorem closure_indirect_call_correspondence_M {M : Type} [Gen.Memory M] [MemoryOps M]
    {p : ProvenancePtr} {m : Machine M} {fnNm : Gen.FnName} {addr : Nat}
    {prov : Option (Gen.Memory.Provenance M)} {c : CapturedMir} {mode : ClosureEnvMode} {fn : Gen.Function}
    {n : Nat}
    (s : MachineState) (callerBody : CapturedMir) (func : MirAst.Operand) (argOps : List MirAst.Operand)
    (dest : MirAst.Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction) (span : String)
    (localsAfterFunc locals' : List LocalSlot) (argVals : List MirSemantics.Value)
    (hRel : ClosureFnPtrEntryRel s.memory p m fnNm addr prov c mode fn n)
    (hNotDir : extractCalleeDefPath? func = none)
    (hFunc : evalOperandWithBodyCast s.frame.locals func s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack =
      .ok (.ptr p 8) localsAfterFunc)
    (hCompatSite : ∀ e, lookupFnPtr s.memory.fnPtrs p.allocId = some e →
      fnEntryCompatibleWithCallSite e (length argOps) (operandTy callerBody.localDecls callerBody.layouts func) = true)
    (hArgs : evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
      callerBody.layouts s.memory.callerLocals callerBody.localDecls s.memory.callStack = .ok argVals locals')
    (hLook : lookupCallee s.memory.callees callerBody.layouts c.defPath [] s.memory.traitImpls = some c)
    (spa : StackPopAction M) (callerRetTy : Gen.Type) (callerArgs : List (Gen.Value M × Gen.Type))
    (f1 f2 : StackFrame M) (cm1 cm2 : ConcurrentMemory M) (calleeRetTy : Gen.Type)
    (hSL : storageLiveM { func := fn, locals := ⟨[]⟩, stack_pop_action := spa, next_block := fn.start, next_stmt := 0, extra := MemoryOps.new_call } m.mem fn.ret = .ok (f1, cm1))
    (hAA : allocFrameArgsM f1 cm1 fn.args = .ok (f2, cm2))
    (hRet : mapIndex f2.func.locals f2.func.ret "func.locals[func.ret]" = .ok calleeRetTy)
    (hAbi : checkAbiCompatibility callerRetTy calleeRetTy = .ok true)
    (hLen : callerArgs.length = length argVals) :
    fnFromPtrM m (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok fn ∧
    (∃ e, lookupFnPtr s.memory.fnPtrs p.allocId = some e ∧
      resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true } localsAfterFunc) ∧
    (length argVals = n →
      (∀ e, lookupFnPtr s.memory.fnPtrs p.allocId = some e →
        checkClosureTargetCompatible { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true }
          c n = true) →
      evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
        MirStepNode.step (pushCalleeFrame s callerBody locals' dest targetBb c
          (synthesizeClosureEnvArg mode (layoutPointerBytes c.layouts) :: argVals) unwind) ∧
      createFrameM m fn spa .Rust callerRetTy callerArgs =
        (initFrameArgsM { m with mem := cm2 } f2 fn.args callerArgs).map (fun m' => (f2, m'))) ∧
    (length argVals = n + 1 →
      evalTerminator s { kind := .call func argOps dest (some targetBb) unwind, span := span } (some callerBody) =
        MirStepNode.fail .ub ∧
      createFrameM m fn spa .Rust callerRetTy callerArgs =
        .error (.ub "call ABI violation: number of arguments does not agree")) := by
  obtain ⟨e, hEntry, hDp, hTargs⟩ := hRel.fnEntry
  obtain ⟨hOff, hNoB, _, _⟩ := hRel.entry
  let target : ResolvedCallTarget := { defPath := c.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true }
  have hRes : resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
      .ok target localsAfterFunc := by
    have hCompat := hCompatSite e hEntry
    unfold resolveCallTarget
    simp only [hNotDir, hFunc, hOff, hNoB, hEntry, hCompat, hDp, hTargs, Nat.beq_refl, Bool.and_self]
    rfl
  have hLaw := minirust_createFrameM_arity_law m fn spa callerRetTy callerArgs f1 f2 cm1 cm2 calleeRetTy hSL hAA
    hRet hAbi
  rw [hRel.mrConv] at hLaw
  refine ⟨hRel.mrResolve, ⟨e, hEntry, hRes⟩, fun h1 hCompat => ⟨?_, ?_⟩, fun h2 => ⟨?_, ?_⟩⟩
  · exact (closure_indirect_call_prepends_env s callerBody func argOps dest targetBb unwind span target
      localsAfterFunc locals' argVals c mode hRes rfl hArgs hLook hRel.shape
      (by rw [h1]; exact hCompat e hEntry)).1
  · exact hLaw.2.1 (by rw [hRel.mrArity, hLen, h1])
  · exact (closure_indirect_call_fail_closed s callerBody func argOps dest targetBb unwind span target
      localsAfterFunc locals' argVals c hRes rfl hArgs hLook
      (Or.inr (Or.inl ⟨mode, hRel.shape, by rw [h2, hRel.trustedArity]⟩))).2.1
  · exact hLaw.1 (by rw [hRel.mrArity, hLen, h2]; exact Nat.ne_of_lt (Nat.lt_succ_self n))

/-! ## §3. MiniRust Reference Programs (`Mach` & `MachTB`)

MiniRust has no closure types (and upstream `tooling/minimize/src/rvalue.rs`
explicitly leaves `ClosureFnPointer` unimplemented):

> "| smir::CastKind::PointerCoercion(smir::PointerCoercion::ClosureFnPointer(..)) => rs::span_bug!(span, \"cast not supported: {cast_kind:?}\"),"

A non-capturing closure coerced to a function pointer is modeled as a `Function`
of the closure's *user-visible* arity `N` registered in `Machine::fn_ptrs`,
`ClosureFnPointer(Safe|Unsafe)` is `Constant::FnPointer`, `UnsafeFnPointer` and
`FnPtrToPtr` are type-erasing `Transmute`s (MiniRust erases function-pointer
safety), and an indirect call is `Terminator::Call` on the loaded pointer
followed by the callee's `Terminator::Return` (which is also the reference
lowering of `TerminatorKind::TailCall` and of the runtime arm of
`const_eval_select`). Each root function ends in a self-loop, so the observed
return local `_0` (allocation `0`) is stable under extra steps. -/

def cfLd (i : Nat) : ValueExpr := .Load (.Local (localName i))
def cfLc (i : Nat) : PlaceExpr := .Local (localName i)
def cfU32 (n : Int) : ValueExpr := .Constant (.Int n) u32MrTy
def cfBlk (ss : List Gen.Statement) (t : Gen.Terminator) : Gen.BasicBlock := ⟨ss, t, .Regular⟩
/-- The final self-loop block. -/
def cfLoopBb (i : Nat) : Gen.BbName × Gen.BasicBlock := (bbName i, cfBlk [] (.Goto (bbName i)))
/-- `Constant::FnPointer` of program function `i` (the MiniRust image of
`ReifyFnPointer` and `ClosureFnPointer`; `spec/lang/step/expressions.md`):
> "Constant::FnPointer(fn_name) => {
>     let ptr = self.fn_ptrs[fn_name];
>     Value::Ptr(ptr.widen(None))
> }" -/
def cfFnPtrC (i : Nat) : ValueExpr := .Constant (.FnPointer (fnName i)) thinRawPtrTy
def cfBin (op : IntBinOp) (a b : ValueExpr) : ValueExpr := .BinOp (.Int op) a b
/-- A type-erasing pointer `Transmute` (`UnsafeFnPointer`, `FnPtrToPtr`;
`tooling/minimize/src/rvalue.rs`):
> "smir::CastKind::Transmute
> | smir::CastKind::FnPtrToPtr
> | smir::CastKind::PointerCoercion(smir::PointerCoercion::UnsafeFnPointer) => {
>     let operand = self.translate_operand_smir(operand, span);
>     let ty = self.translate_ty_smir(*cast_ty, span);
>     build::transmute(operand, ty)
> }" -/
def cfPtrCast (v : ValueExpr) : ValueExpr := .UnOp (.Cast (.Transmute thinRawPtrTy)) v
/-- `ret = callee(args) -> bb next` with calling convention `conv`, checking
calling convention, return type, arity, and argument types in `create_frame`
(`spec/lang/step/terminators.md`):
> "if caller_conv != func.calling_convention {
>     throw_ub!(\"call ABI violation: calling conventions are not the same\");
> }
> if !check_abi_compatibility(caller_ret_ty, func.locals[func.ret]) {
>     throw_ub!(\"call ABI violation: return types are not compatible\");
> }
> if func.args.len() != caller_args.len() {
>     throw_ub!(\"call ABI violation: number of arguments does not agree\");
> }
> for (callee_local, (caller_val, caller_ty)) in func.args.zip(caller_args) {
>     if !check_abi_compatibility(caller_ty, func.locals[callee_local]) {
>         throw_ub!(\"call ABI violation: argument types are not compatible\");
>     }" -/
def cfCall (callee : ValueExpr) (args : List ValueExpr) (ret next : Nat)
    (conv : CallingConvention := .Rust) : Gen.Terminator :=
  .Call callee conv (args.map .ByValue) (cfLc ret) (some (bbName next)) none

/-- A MiniRust function of user-visible arity `n` over `u32`: `_0 = body; return`. -/
def cfMrLeafFn (n : Nat) (body : ValueExpr) : Gen.Function :=
  mkMrFn ((localName 0, u32MrTy) :: (List.range n).map fun i => (localName (i + 1), u32MrTy))
    ((List.range n).map fun i => localName (i + 1)) (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 0) body] .Return)]

/-- Stack allocations of the root frame's locals, numbered from `i`. -/
def cfMrLocalAllocs : Nat → List (List Byte × Nat) → List Gen.Allocation
  | _, [] => []
  | i, (bs, al) :: rest => mkStackAlloc (128 * (i + 1)) bs al :: cfMrLocalAllocs (i + 1) rest

/-- A reference machine: the root frame runs `fns[0]` with locals `_0.._{k-1}`
backed by allocations `0..k-1` (initial bytes and alignment from `locals`);
program function `i` is registered in `fn_ptrs` at address `4096 * (i + 1)`
with the provenance of its function allocation `k + i`. -/
def cfMrMach (fns : List Gen.Function) (locals : List (List Byte × Nat)) : Mach :=
  mkMrMach (mkMrProg (fns.zipIdx.map fun (f, i) => (fnName i, f)))
    (cfMrLocalAllocs 0 locals ++ (List.range fns.length).map fun i => mkFnAlloc (Int.ofNat (4096 * (i + 1))))
    [mkRootFrame (fns.headD (mkMrFn [] [] (localName 0) []))
      ((List.range locals.length).map fun i => (localName i, ⟨128 * (i + 1), some (⟨i⟩, ())⟩))]
    ((List.range fns.length).map fun i => (fnName i, ⟨4096 * (i + 1), some (⟨locals.length + i⟩, ())⟩))

/-- `n` uninitialized bytes. -/
def cfU (n : Nat) : List Byte := List.replicate n .Uninit
/-- Bytes of a `u32`. -/
def cfU32B (n : Nat) : List Byte := scalarBytes u32 n

/-- **Three-way MiniRust agreement on a `u32` result**: after `fuel` steps the
return local `_0` (allocation `0`) holds `v` on `Mach` (`BasicMemory`) AND on
`MachTB` (`TreeBorrowsMemory`), where the final `MachTB` state satisfies
`MachTB.wfLive`. -/
def CfMrAgrees (fuel : Nat) (m : Mach) (v : Nat) : Prop :=
  (∃ m', Interp.steps fuel m = .ok m' ∧ m'.mem.memory.allocations[0]?.map (·.data) = some (cfU32B v)) ∧
  (∃ m', Interp.stepsTB fuel (liftMachToTB m) = .ok m' ∧ MachTB.wfLive m' ∧
    m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
      some ((cfU32B v).map (projByteTB ∘ liftByteTB)))

theorem cfMrAgrees_of_decide {fuel : Nat} {m : Mach} {v : Nat}
    (h1 : (Interp.steps fuel m).toOption.map (fun m' => m'.mem.memory.allocations[0]?.map (·.data)) =
      some (some (cfU32B v)))
    (h2 : (Interp.stepsTB fuel (liftMachToTB m)).toOption.map
        (fun m' => m'.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB)) =
      some (some ((cfU32B v).map (projByteTB ∘ liftByteTB)))) : CfMrAgrees fuel m v :=
  ⟨ok_of_map_toOption h1, ok_stepsTB_wfLive h2⟩

/-- **MiniRust UB on both memories** with the exact message `msg`. -/
def CfMrUb (fuel : Nat) (m : Mach) (msg : String) : Prop :=
  Interp.steps fuel m = .error (.ub msg) ∧ Interp.stepsTB fuel (liftMachToTB m) = .error (.ub msg)

theorem cfMrUb_of_decide {fuel : Nat} {m : Mach} {msg : String}
    (h1 : interpUbMsg (Interp.steps fuel m) = some msg)
    (h2 : interpUbMsg (Interp.stepsTB fuel (liftMachToTB m)) = some msg) : CfMrUb fuel m msg :=
  ⟨eq_error_ub_of_interpUbMsg h1, eq_error_ub_of_interpUbMsg h2⟩

/-- Root caller of an `n`-argument closure function pointer:
`_{n+1} = FnPointer(fns[1]); _0 = (*_{n+1})(_1, .., _n)` (then loop). -/
def cfMrIndirectCaller (n : Nat) : Gen.Function :=
  mkMrFn ((localName 0, u32MrTy) :: ((List.range n).map fun i => (localName (i + 1), u32MrTy)) ++
      [(localName (n + 1), thinRawPtrTy)])
    ((List.range n).map fun i => localName (i + 1)) (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc (n + 1)) (cfFnPtrC 1)]
        (cfCall (cfLd (n + 1)) ((List.range n).map fun i => cfLd (i + 1)) 0 1)),
     cfLoopBb 1]

/-- The machine coercing the arity-`args.length` closure function `closureFn`
to a function pointer and calling it on `args`. -/
def cfMrIndirectMach (closureFn : Gen.Function) (args : List Nat) : Mach :=
  cfMrMach [cfMrIndirectCaller args.length, closureFn]
    ((cfU 4, 4) :: (args.map fun a => (cfU32B a, 4)) ++ [(cfU 8, 8)])

/-- `widen_and_identity`: `f = FnPointer; g = f as unsafe fn; raw_c = f as *const ();
raw_d = g as *const (); same = (raw_c == raw_d) as u32; _0 = g(x) ^ (same << 8)`. -/
def cfMrWidenCaller : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, thinRawPtrTy), (localName 3, thinRawPtrTy),
      (localName 4, thinRawPtrTy), (localName 5, thinRawPtrTy), (localName 6, u32MrTy), (localName 7, u32MrTy)]
    [localName 1] (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 2) (cfFnPtrC 1), .Assign (cfLc 3) (cfPtrCast (cfLd 2)),
        .Assign (cfLc 4) (cfPtrCast (cfLd 2)), .Assign (cfLc 5) (cfPtrCast (cfLd 3))]
        (.Switch (.UnOp (.Cast (.Transmute u8MrTy)) (.BinOp (.Rel .Eq) (cfLd 4) (cfLd 5))) ⟨[(1, bbName 1)]⟩
          (bbName 2))),
     (bbName 1, cfBlk [.Assign (cfLc 6) (cfU32 1)] (.Goto (bbName 3))),
     (bbName 2, cfBlk [.Assign (cfLc 6) (cfU32 0)] (.Goto (bbName 3))),
     (bbName 3, cfBlk [] (cfCall (cfLd 3) [cfLd 1] 7 4)),
     (bbName 4, cfBlk [.Assign (cfLc 0) (cfBin .BitXor (cfLd 7) (cfBin .Shl (cfLd 6) (cfU32 8)))]
        (.Goto (bbName 5))),
     cfLoopBb 5]

def cfMrWidenMach (x : Nat) : Mach :=
  cfMrMach [cfMrWidenCaller, cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 1))]
    [(cfU 4, 4), (cfU32B x, 4), (cfU 8, 8), (cfU 8, 8), (cfU 8, 8), (cfU 8, 8), (cfU 4, 4), (cfU 4, 4)]

/-- `mixed_fn_item_and_closure`: `a = FnPointer(helper_triple); b = FnPointer(closure);
_0 = a(x) ^ b(x)`. -/
def cfMrMixedCaller : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, thinRawPtrTy), (localName 3, thinRawPtrTy),
      (localName 4, u32MrTy), (localName 5, u32MrTy)] [localName 1] (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 2) (cfFnPtrC 1), .Assign (cfLc 3) (cfFnPtrC 2)] (cfCall (cfLd 2) [cfLd 1] 4 1)),
     (bbName 1, cfBlk [] (cfCall (cfLd 3) [cfLd 1] 5 2)),
     (bbName 2, cfBlk [.Assign (cfLc 0) (cfBin .BitXor (cfLd 4) (cfLd 5))] (.Goto (bbName 3))),
     cfLoopBb 3]

def cfMrMixedMach (x : Nat) : Mach :=
  cfMrMach [cfMrMixedCaller, cfMrLeafFn 1 (cfBin .Mul (cfLd 1) (cfU32 3)), cfMrLeafFn 1 (cfBin .Mul (cfLd 1) (cfU32 5))]
    [(cfU 4, 4), (cfU32B x, 4), (cfU 8, 8), (cfU 8, 8), (cfU 4, 4), (cfU 4, 4)]

/-- `PairU32 { a: u32, b: u32 }` (`#[repr(C)]`, size 8, alignment 4). -/
@[reducible] def cfPairMrTy : Gen.Type := .Tuple [(⟨0⟩, u32MrTy), (⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none
@[reducible] def cfPairPointee : PointeeInfo :=
  { layout := .Sized ⟨8⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true, unpin := true }
/-- `&PairU32`. -/
@[reducible] def cfPairRefMrTy : Gen.Type := .Ptr (.Ref .Immutable cfPairPointee)

/-- `StorageLive(_1); ..; StorageLive(_n)`. -/
def cfLives (n : Nat) : List Gen.Statement := (List.range n).map fun i => .StorageLive (localName (i + 1))

/-- MiniRust reference of `__anneal_vt_driver_61873(seed, bias)` (program
function `1`; closures `|z| z + 17` and `|z| z ^ 17` are functions `2` and `3`):
`cfp = FnPointer(2); cufp = cfp as unsafe fn; cufp_direct = FnPointer(3);
raw_c = cfp as *const (); raw_d = cufp as *const (); first = cfp(seed);
second = cufp(first ^ bias); third = cufp_direct(second ^ 24);
same = (raw_c == raw_d) as u32;
first ^ (second << 1) ^ (third << 2) ^ same`. -/
def cfMrFindingDriver : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, u32MrTy), (localName 3, thinRawPtrTy),
      (localName 4, thinRawPtrTy), (localName 5, thinRawPtrTy), (localName 6, thinRawPtrTy),
      (localName 7, thinRawPtrTy), (localName 8, u32MrTy), (localName 9, u32MrTy), (localName 10, u32MrTy),
      (localName 11, u32MrTy)] [localName 1, localName 2] (localName 0)
    [(bbName 0, cfBlk ((List.range 9).map (fun i => Gen.Statement.StorageLive (localName (i + 3))) ++
        [.Assign (cfLc 3) (cfFnPtrC 2), .Assign (cfLc 4) (cfPtrCast (cfLd 3)), .Assign (cfLc 5) (cfFnPtrC 3),
         .Assign (cfLc 6) (cfPtrCast (cfLd 3)), .Assign (cfLc 7) (cfPtrCast (cfLd 4))])
        (cfCall (cfLd 3) [cfLd 1] 8 1)),
     (bbName 1, cfBlk [] (cfCall (cfLd 4) [cfBin .BitXor (cfLd 8) (cfLd 2)] 9 2)),
     (bbName 2, cfBlk [] (cfCall (cfLd 5) [cfBin .BitXor (cfLd 9) (cfU32 24)] 10 3)),
     (bbName 3, cfBlk [] (.Switch (.UnOp (.Cast (.Transmute u8MrTy)) (.BinOp (.Rel .Eq) (cfLd 6) (cfLd 7)))
        ⟨[(1, bbName 4)]⟩ (bbName 5))),
     (bbName 4, cfBlk [.Assign (cfLc 11) (cfU32 1)] (.Goto (bbName 6))),
     (bbName 5, cfBlk [.Assign (cfLc 11) (cfU32 0)] (.Goto (bbName 6))),
     (bbName 6, cfBlk [.Assign (cfLc 0) (cfBin .BitXor (cfBin .BitXor (cfBin .BitXor (cfLd 8)
        (cfBin .Shl (cfLd 9) (cfU32 1))) (cfBin .Shl (cfLd 10) (cfU32 2))) (cfLd 11))] .Return)]

/-- MiniRust reference of
`pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27` (program
function `4`): `pair = PairU32 { a: 7, b: 35 }; tmp = &pair;
raw = &raw const (*tmp).b; shared = &*tmp; first = *raw; again = *raw;
tail = first ^ shared.a ^ (again << 8);
tail ^ __anneal_vt_driver_61873(first & 0xFFFF, 24)`. The two shared
references are validated (retagged) when created. -/
def cfMrFindingMain : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, cfPairMrTy), (localName 2, cfPairRefMrTy),
      (localName 3, thinRawPtrTy), (localName 4, cfPairRefMrTy), (localName 5, u32MrTy), (localName 6, u32MrTy),
      (localName 7, u32MrTy), (localName 8, u32MrTy)] [] (localName 0)
    [(bbName 0, cfBlk (cfLives 8 ++
        [.Assign (cfLc 1) (.Tuple [cfU32 7, cfU32 35] cfPairMrTy),
         .Assign (cfLc 2) (.AddrOf (cfLc 1) (.Ref .Immutable cfPairPointee)),
         .Validate (cfLc 2) false,
         .Assign (cfLc 3) (.AddrOf (.Field (.Deref (cfLd 2) cfPairMrTy) 1) (.Raw .None)),
         .Assign (cfLc 4) (.AddrOf (.Deref (cfLd 2) cfPairMrTy) (.Ref .Immutable cfPairPointee)),
         .Validate (cfLc 4) false,
         .Assign (cfLc 5) (.Load (.Deref (cfLd 3) u32MrTy)),
         .Assign (cfLc 6) (.Load (.Deref (cfLd 3) u32MrTy)),
         .Assign (cfLc 7) (cfBin .BitXor (cfBin .BitXor (cfLd 5) (.Load (.Field (.Deref (cfLd 4) cfPairMrTy) 0)))
           (cfBin .Shl (cfLd 6) (cfU32 8)))])
        (cfCall (cfFnPtrC 1) [cfBin .BitAnd (cfLd 5) (cfU32 65535), cfU32 24] 8 1)),
     (bbName 1, cfBlk [.Assign (cfLc 0) (cfBin .BitXor (cfLd 7) (cfLd 8))] .Return)]

/-- Root harness: `_0 = fns[callee](args)` (then loop). -/
def cfMrHarness (callee : Nat) (args : List ValueExpr) : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy)] [] (localName 0)
    [(bbName 0, cfBlk [] (cfCall (cfFnPtrC callee) args 0 1)), cfLoopBb 1]

/-- The `finding_0007` reference machine: program functions `1` = driver,
`2` = `{closure#0}` (`z + 17`), `3` = `{closure#1}` (`z ^ 17`), `4` = main;
the root harness calls the main function (`runMain = true`) or the driver on
`(35, 24)`. -/
def cfMrFindingMach (runMain : Bool) : Mach :=
  cfMrMach [if runMain then cfMrHarness 4 [] else cfMrHarness 1 [cfU32 35, cfU32 24], cfMrFindingDriver,
      cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17)), cfMrLeafFn 1 (cfBin .BitXor (cfLd 1) (cfU32 17)),
      cfMrFindingMain]
    [(cfU 4, 4)]

/-- The zero-sized MiniRust image of a non-capturing closure value (`()`-like
empty tuple, size `0`, alignment `1`). -/
@[reducible] def cfZstMrTy : Gen.Type := .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- The generic identity `id_mut::<{closure}>` / `id_once::<{closure}>` at the
zero-sized closure type: `_0 = _1; return`. -/
def cfMrZstIdFn : Gen.Function :=
  mkMrFn [(localName 0, cfZstMrTy), (localName 1, cfZstMrTy)] [localName 1] (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 0) (cfLd 1)] .Return)]

/-- Root caller of `fn_mut_kind` / `fn_once_kind`: `c = {closure}; c = id(c);
f = FnPointer(closure); _0 = f(x)` (then loop); program function `1` is the
identity and `2` the closure function. -/
def cfMrIdThenIndirectCaller : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, thinRawPtrTy), (localName 3, cfZstMrTy),
      (localName 4, cfZstMrTy)] [localName 1] (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 3) (.Tuple [] cfZstMrTy)]
        (.Call (cfFnPtrC 1) .Rust [.ByValue (cfLd 3)] (cfLc 4) (some (bbName 1)) none)),
     (bbName 1, cfBlk [.Assign (cfLc 2) (cfFnPtrC 2)] (cfCall (cfLd 2) [cfLd 1] 0 2)),
     cfLoopBb 2]

def cfMrIdThenIndirectMach (closureFn : Gen.Function) (x : Nat) : Mach :=
  cfMrMach [cfMrIdThenIndirectCaller, cfMrZstIdFn, closureFn]
    [(cfU 4, 4), (cfU32B x, 4), (cfU 8, 8), ([], 1), ([], 1)]

/-! ## §4. Concrete Kernel-Checked Three-Way Witnesses on Verbatim `rustc-capture` Bodies

Every Trusted side below executes a verbatim `rustc-capture` body of §0 through
`stepMirFn` (`cfRun`); every MiniRust side executes the reference program of §3
through `MiniRustSpec.Interp.{steps, stepsTB}` on `Mach` and `MachTB`
(`CfMrAgrees`, including `MachTB.wfLive`). -/

/-- **`Fn` closure (`_1 : &{closure}`)**: `fn_shared(5) = 22`. The Trusted
closure body has `argCount = 2` (environment + `a`); the MiniRust closure
function has arity `1`. -/
theorem cf_fn_closure_three_way_witness :
    calleeOwnClosureShape? cfFx_fn_shared_closure_0 = some (.nonCapturing .sharedRef) ∧
    cfFx_fn_shared_closure_0.argCount = 2 ∧
    (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))).args.length = 1 ∧
    cfRun cfFx_fn_shared 64 (cfInit cfFx_fn_shared [cfU32V 5] [cfFx_fn_shared_closure_0]) = .scalar 22 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [5]) 22 :=
  ⟨cfShapeTag_inj (by decide +kernel), rfl, rfl, by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **`FnMut` closure (`_1 : &mut {closure}`)**: `fn_mut_kind(5) = 7`. The
closure first passes through the generic identity `id_mut` (linked on the
Trusted side; a zero-sized `Call`/`Return` in the MiniRust reference
program). -/
theorem cf_fnMut_closure_three_way_witness :
    calleeOwnClosureShape? cfFx_fn_mut_kind_closure_0 = some (.nonCapturing .mutRef) ∧
    cfFx_fn_mut_kind_closure_0.argCount = 2 ∧
    cfRun cfFx_fn_mut_kind 96 (cfInit cfFx_fn_mut_kind [cfU32V 5] [cfFx_id_mut, cfFx_fn_mut_kind_closure_0]) =
      .scalar 7 4 ∧
    CfMrAgrees 12 (cfMrIdThenIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 2))) 5) 7 :=
  ⟨cfShapeTag_inj (by decide +kernel), rfl, by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **`FnOnce` closure (`_1 : {closure}` by value)**: `fn_once_kind(5) = 8`
(through the generic identity `id_once`, as for `FnMut`). -/
theorem cf_fnOnce_closure_three_way_witness :
    calleeOwnClosureShape? cfFx_fn_once_kind_closure_0 = some (.nonCapturing .byValue) ∧
    cfFx_fn_once_kind_closure_0.argCount = 2 ∧
    cfRun cfFx_fn_once_kind 96 (cfInit cfFx_fn_once_kind [cfU32V 5] [cfFx_id_once, cfFx_fn_once_kind_closure_0]) =
      .scalar 8 4 ∧
    CfMrAgrees 12 (cfMrIdThenIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 3))) 5) 8 :=
  ⟨cfShapeTag_inj (by decide +kernel), rfl, by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **Zero-argument and two-argument closures**: `zero_arg() = 7` (Trusted
`argCount = 1`, MiniRust arity `0`) and `two_arg(6, 3) = 5` (Trusted
`argCount = 3`, MiniRust arity `2`). -/
theorem cf_zero_and_two_arg_closure_three_way_witness :
    cfFx_zero_arg_closure_0.argCount = 1 ∧ (cfMrLeafFn 0 (cfU32 7)).args.length = 0 ∧
    cfRun cfFx_zero_arg 64 (cfInit cfFx_zero_arg [] [cfFx_zero_arg_closure_0]) = .scalar 7 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 0 (cfU32 7)) []) 7 ∧
    cfFx_two_arg_closure_0.argCount = 3 ∧ (cfMrLeafFn 2 (cfBin .BitXor (cfLd 1) (cfLd 2))).args.length = 2 ∧
    cfRun cfFx_two_arg 64 (cfInit cfFx_two_arg [cfU32V 6, cfU32V 3] [cfFx_two_arg_closure_0]) = .scalar 5 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 2 (cfBin .BitXor (cfLd 1) (cfLd 2))) [6, 3]) 5 :=
  ⟨rfl, rfl, by decide +kernel, cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel),
   rfl, rfl, by decide +kernel, cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **`ClosureFnPointer(Unsafe)`**: `unsafe_closure(5) = 5 ^ 17 = 20`
(direct coercion to an `unsafe fn` pointer, called in `unsafe`). -/
theorem cf_unsafe_closure_three_way_witness :
    cfRun cfFx_unsafe_closure 64 (cfInit cfFx_unsafe_closure [cfU32V 5] [cfFx_unsafe_closure_closure_0]) =
      .scalar 20 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .BitXor (cfLd 1) (cfU32 17))) [5]) 20 :=
  ⟨by decide +kernel, cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **`ClosureFnPointer(Safe)` + `UnsafeFnPointer` + `FnPtrToPtr` pointer
identity (`raw_c == raw_d`)**: `widen_and_identity(5) = (5 + 1) ^ (1 << 8) = 262`
on Trusted, `Mach`, and `MachTB`: bit `8` of the result is the outcome of
`(f as *const ()) == (g as *const ())`, and on `Mach` the two raw-pointer
locals `raw_c` (allocation `4`) and `raw_d` (allocation `5`) hold the same
pointer bytes (address `8192`, the closure function's allocation `9`). -/
theorem cf_widen_and_identity_three_way_witness :
    cfRun cfFx_widen_and_identity 128 (cfInit cfFx_widen_and_identity [cfU32V 5] [cfFx_widen_and_identity_closure_0]) =
      .scalar 262 4 ∧
    CfMrAgrees 16 (cfMrWidenMach 5) 262 ∧
    (∃ m', Interp.steps 16 (cfMrWidenMach 5) = .ok m' ∧
      [4, 5].map (fun i => m'.mem.memory.allocations[i]?.map (·.data)) =
        [some (ptrBytes 8192 (some (⟨9⟩, ()))), some (ptrBytes 8192 (some (⟨9⟩, ())))]) :=
  ⟨by decide +kernel, cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel),
   ok_of_map_toOption (by decide +kernel)⟩

/-- **`TerminatorKind::TailCall` through a closure function pointer**:
`tail_through_closure(9) = 9 ^ 5 = 12` (`become f(x)`; MiniRust reference:
`Call` then `Return`). -/
theorem cf_tailCall_closure_three_way_witness :
    cfRun cfFx_tail_through_closure 64
        (cfInit cfFx_tail_through_closure [cfU32V 9] [cfFx_tail_through_closure_closure_0]) = .scalar 12 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .BitXor (cfLd 1) (cfU32 5))) [9]) 12 :=
  ⟨by decide +kernel, cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **Mixed `fn`-item (`ReifyFnPointer`) and closure (`ClosureFnPointer`)
coercions in one body**: `mixed_fn_item_and_closure(4) = (4 * 3) ^ (4 * 5) = 24`.
The `fn` item is not closure-shaped (`argCount = 1`, no environment) while the
closure body is. -/
theorem cf_mixed_fnItem_and_closure_three_way_witness :
    calleeOwnClosureShape? cfFx_helper_triple = none ∧ cfFx_helper_triple.argCount = 1 ∧
    calleeOwnClosureShape? cfFx_mixed_fn_item_and_closure_closure_0 = some (.nonCapturing .sharedRef) ∧
    cfRun cfFx_mixed_fn_item_and_closure 128 (cfInit cfFx_mixed_fn_item_and_closure [cfU32V 4]
      [cfFx_helper_triple, cfFx_mixed_fn_item_and_closure_closure_0]) = .scalar 24 4 ∧
    CfMrAgrees 16 (cfMrMixedMach 4) 24 :=
  ⟨cfShapeTag_inj (by decide +kernel), rfl, cfShapeTag_inj (by decide +kernel), by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-! ### Hand-built call sites over the verbatim closure bodies

The following callers reuse the layouts and ABI of the verbatim `fn_shared`
capture and replace only its blocks, so that a function pointer obtained
elsewhere (`cfEntry`, at the first synthetic function allocation `65536`) can
be called with a chosen signature, argument list, or calling convention. -/

@[reducible] def cfU32K : RigidTy := .uint .u32
/-- `fn(u32) -> u32`. -/
@[reducible] def cfFnU32 : RigidTy := .fnPtr [cfU32K] cfU32K .safe .rust
def cfSharedPath : String := "closure_matrix::fn_shared::{closure#0}"
def cfCapPath : String := "closure_matrix::capturing_direct::{closure#0}"
def cfCapZstPath : String := "closure_matrix::capturing_direct::{closure#1}"
@[reducible] def cfSharedClo : RigidTy := .closure cfSharedPath []
/-- `{closure}` capturing a `u32`. -/
@[reducible] def cfCapClo : RigidTy := .closure cfCapPath [cfU32K]
/-- `{closure}` capturing the zero-sized `()`. -/
@[reducible] def cfCapZstClo : RigidTy := .closure cfCapZstPath [.tuple []]
def cfDecl (k : RigidTy) (idx : Nat) : MirAst.LocalDecl :=
  { mutability := .mut, ty := { kind := k, layoutIdx := idx }, debugName := none }
/-- Function-pointer value at the synthetic allocation `65536`. -/
def cfFnPtrVal : MirSemantics.Value := .ptr { allocId := 65536, offsetBytes := 0 } 8
/-- Environment value passed explicitly by forged or direct calls. -/
def cfEnvScalar : MirSemantics.Value := .scalar ⟨1, 8⟩
/-- `FnPtrEntry` at `65536` naming `p` with signature `sig` (no closure flag). -/
def cfEntry (p : String) (sig : RigidTy) : FnPtrEntry := { allocId := 65536, defPath := p, fnSig := some sig }
def cfRetBlock : MirAst.BasicBlockData :=
  { statements := [], terminator := { kind := .return_, span := "ret" }, isCleanup := false }

/-- `fn(_1 : sigKind, _2 : argKind) -> u32 { _0 = _1(_2) }`. -/
def cfPtrCaller (sigKind : RigidTy) (argKind : RigidTy := cfU32K) : CapturedMir :=
  { cfFx_fn_shared with
    defPath := "cf::ptr_caller", argCount := 2,
    localDecls := [cfDecl cfU32K 0, cfDecl sigKind 1, cfDecl argKind 0],
    basicBlocks :=
      [{ statements := [],
         terminator := { kind := .call (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) (some 1) .continue_,
                         span := "ptr_call" },
         isCleanup := false }, cfRetBlock] }

/-- `fn(_1 : sigKind, _2 : envKind, _3 : u32) -> u32 { _0 = _1(_2, _3) }`: a
forged `(N + 1)`-argument call passing the closure environment explicitly. -/
def cfEnvPtrCaller (sigKind envKind : RigidTy) : CapturedMir :=
  { cfFx_fn_shared with
    defPath := "cf::env_ptr_caller", argCount := 3,
    localDecls := [cfDecl cfU32K 0, cfDecl sigKind 1, cfDecl envKind 1, cfDecl cfU32K 0],
    basicBlocks :=
      [{ statements := [],
         terminator := { kind := .call (.copy (locPlace 1)) [.copy (locPlace 2), .copy (locPlace 3)] (locPlace 0)
                           (some 1) .continue_,
                         span := "env_ptr_call" },
         isCleanup := false }, cfRetBlock] }

/-- `fn(_1 : envKind, _2 : u32) -> u32 { _0 = p(_1, _2) }`: a direct
(`isIndirect = false`) call of the closure body `p` passing its environment. -/
def cfDirectEnvCaller (p : String) (envKind : RigidTy) : CapturedMir :=
  { cfFx_fn_shared with
    defPath := "cf::direct_env_caller", argCount := 2,
    localDecls := [cfDecl cfU32K 0, cfDecl envKind 1, cfDecl cfU32K 0],
    basicBlocks :=
      [{ statements := [],
         terminator :=
           { kind := .call (.constant { ty := { kind := .fnDef p [], layoutIdx := 2 }, val := .zeroSized })
               [.copy (locPlace 1), .copy (locPlace 2)] (locPlace 0) (some 1) .continue_,
             span := "direct_env_call" },
         isCleanup := false }, cfRetBlock] }

/-- `fn(_1 : u32, _2 : rtKind) -> u32 { _3 = (copy _1,); _0 = const_eval_select(move _3, ct_add, copy _2) }`:
an inline `core::intrinsics::const_eval_select` with runtime target `_2`. -/
def cfCesCaller (rtKind : RigidTy) : CapturedMir :=
  { cfFx_fn_shared with
    defPath := "cf::ces_caller", argCount := 2,
    localDecls := [cfDecl cfU32K 0, cfDecl cfU32K 0, cfDecl rtKind 1, cfDecl (.tuple [cfU32K]) 0],
    basicBlocks :=
      [{ statements :=
           [{ kind := .storageLive 3, span := "ces_live" },
            { kind := .assign (locPlace 3) (.aggregate .tuple [.copy (locPlace 1)]), span := "ces_args" }],
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "core::intrinsics::const_eval_select"
                                      [.tuple [cfU32K], .fnDef "closure_matrix::ct_add" [], rtKind, cfU32K],
                                    layoutIdx := 2 }, val := .zeroSized })
               [.move (locPlace 3),
                .constant { ty := { kind := .fnDef "closure_matrix::ct_add" [], layoutIdx := 2 }, val := .zeroSized },
                .copy (locPlace 2)]
               (locPlace 0) (some 1) .continue_,
             span := "ces_call" },
         isCleanup := false }, cfRetBlock] }

/-- **`const_eval_select` with a closure function pointer as runtime target**:
the inline intrinsic call `const_eval_select((5,), ct_add, rt)` dispatches to
the closure body with the environment prepended (`22`), and the verbatim
`ces_through_closure_fn_ptr(4)` capture (where `rustc` lowered the intrinsic
to an indirect call) returns `21`; MiniRust reference: the runtime arm
`rt(x)`. -/
theorem cf_constEvalSelect_closure_three_way_witness :
    cfRun (cfCesCaller cfFnU32) 32 (cfInitPtrs (cfCesCaller cfFnU32) [cfU32V 5, cfFnPtrVal]
      [cfFx_fn_shared_closure_0] [cfEntry cfSharedPath cfFnU32]) = .scalar 22 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [5]) 22 ∧
    cfRun cfFx_ces_through_closure_fn_ptr 96 (cfInit cfFx_ces_through_closure_fn_ptr [cfU32V 4]
      [cfFx_ces_through_closure_fn_ptr_closure_0]) = .scalar 21 4 ∧
    CfMrAgrees 8 (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [4]) 21 :=
  ⟨by decide +kernel, cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel)⟩

/-- **`finding_0007` parity (Miri: `pass:scalar:9147:4`)** on the verbatim
`rustc-capture` bodies of the difftest reproducer:
`__anneal_vt_driver_61873(35, 24) = 159` and
`pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27() = 9147 : u32`
on Trusted `stepMirFn`, MiniRust `Mach`, and MiniRust `MachTB` (with
`MachTB.wfLive`). Both closures are `Fn` closure bodies (`_1 : &{closure}`,
`argCount = 2`). Without the two linked closure bodies the same Trusted run
stops at an external call to `{closure#0}` — never at `.ub`. -/
theorem cf_finding_0007_parity_three_way_witness :
    calleeOwnClosureShape? cfFx_finding_closure_0 = some (.nonCapturing .sharedRef) ∧
    calleeOwnClosureShape? cfFx_finding_closure_1 = some (.nonCapturing .sharedRef) ∧
    cfFx_finding_closure_0.argCount = 2 ∧ cfFx_finding_closure_1.argCount = 2 ∧
    cfRun cfFx_finding_driver 400 (cfInit cfFx_finding_driver [cfU32V 35, cfU32V 24]
      [cfFx_finding_closure_0, cfFx_finding_closure_1]) = .scalar 159 4 ∧
    CfMrAgrees 40 (cfMrFindingMach false) 159 ∧
    cfRun cfFx_finding_main 600 (cfInit cfFx_finding_main []
      [cfFx_finding_driver, cfFx_finding_closure_0, cfFx_finding_closure_1]) = .scalar 9147 4 ∧
    CfMrAgrees 80 (cfMrFindingMach true) 9147 ∧
    cfRun cfFx_finding_main 600 (cfInit cfFx_finding_main [] [cfFx_finding_driver]) =
      .ext "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}" :=
  ⟨cfShapeTag_inj (by decide +kernel), cfShapeTag_inj (by decide +kernel), rfl, rfl, by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel,
   cfMrAgrees_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel⟩

/-! ## §5. Fail-Closed Negative Witnesses and Instantiations of the Universal Laws -/

/-- Outcome tag of a `PointerCoercion` cast on a single operand local. -/
inductive CfCoerceTag : Type where
  | ok
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Reify local `_0 : opKind` holding `v` to the type `target` via coercion tag
`ck`, through the real `evalRvalue` (`evalReifyFnPointer`), with `callees`
linked. -/
def cfCoerce (ck : String) (opKind : RigidTy) (v : MirSemantics.Value) (target : RigidTy)
    (callees : List CapturedMir) : CfCoerceTag :=
  match evalRvalue [.init v] (.cast (.pointerCoercion ck) (.move (locPlace 0)) { kind := target, layoutIdx := 1 })
      { emptyMemory with callees := callees } [cfDecl opKind 2] cfFx_fn_shared_layouts with
  | .ok _ _ _ => .ok
  | .ub => .ub
  | .unsupported => .unsupported

def cfGenericPath : String := "closure_matrix::generic_closure::{closure#0}"

/-- Numeric code of a closure environment value: `100 + bits * 10 + size` for
a scalar, `1` for the empty aggregate, `0` otherwise. -/
def cfEnvCode : MirSemantics.Value → Nat
  | .scalar sc => 100 + sc.bits * 10 + sc.sizeBytes
  | .aggregate 0 [] => 1
  | _ => 0

/-- Observation of the frame entered by one `stepMirFn` step: (code of `_1`,
bits of `_2`, number of locals, call-stack depth). -/
def cfEntryObs (body : CapturedMir) (s : MachineState) : Option (Nat × Nat × Nat × Nat) :=
  match stepMirFn body s with
  | .tau (.running s') =>
    match s'.frame.locals with
    | _ :: .init e :: .init (.scalar a) :: _ =>
      some (cfEnvCode e, a.bits, length s'.frame.locals, length s'.memory.callStack)
    | _ => none
  | _ => none

/-- Indirect-call state: `cfPtrCaller sig` about to call the pointer at `65536`
(naming `p` with signature `entrySig`) on `arg`, with `callee` linked. -/
def cfPtrCallState (sig : RigidTy) (arg : MirSemantics.Value) (callee : CapturedMir) (p : String)
    (entrySig : RigidTy) (argKind : RigidTy := cfU32K) : MachineState :=
  cfInitPtrs (cfPtrCaller sig argKind) [cfFnPtrVal, arg] [callee] [cfEntry p entrySig]

/-- Forged-call state: `cfEnvPtrCaller` passing the environment explicitly. -/
def cfEnvPtrCallState (clo : RigidTy) (callee : CapturedMir) (p : String) : MachineState :=
  cfInitPtrs (cfEnvPtrCaller (.fnPtr [.ref .not clo, cfU32K] cfU32K .safe .rust) (.ref .not clo))
    [cfFnPtrVal, cfEnvScalar, cfU32V 5] [callee] [cfEntry p (.fnPtr [.ref .not clo, cfU32K] cfU32K .safe .rust)]

/-- MiniRust forged `(N + 1)`-argument call: two arguments passed to the
arity-`1` closure function. -/
def cfMrForgedArityMach : Mach :=
  cfMrMach [cfMrIndirectCaller 2, cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))]
    [(cfU 4, 4), (cfU32B 1, 4), (cfU32B 5, 4), (cfU 8, 8)]

/-- Root caller passing one argument of type `argTy` with calling convention `conv`. -/
def cfMrBadCallCaller (conv : CallingConvention) (argTy : Gen.Type) : Gen.Function :=
  mkMrFn [(localName 0, u32MrTy), (localName 1, argTy), (localName 2, thinRawPtrTy)] [localName 1] (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 2) (cfFnPtrC 1)] (cfCall (cfLd 2) [cfLd 1] 0 1 conv)), cfLoopBb 1]

/-- MiniRust transmuted signature: a `u64` argument passed to the `fn(u32) -> u32`
closure function. -/
def cfMrBadSigMach : Mach :=
  cfMrMach [cfMrBadCallCaller .Rust u64MrTy, cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))]
    [(cfU 4, 4), (scalarBytes ⟨.Unsigned, ⟨8⟩⟩ 5, 8), (cfU 8, 8)]

/-- MiniRust `extern "C"` call of the Rust-ABI closure function. -/
def cfMrExternCMach : Mach :=
  cfMrMach [cfMrBadCallCaller .C u32MrTy, cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))]
    [(cfU 4, 4), (cfU32B 5, 4), (cfU 8, 8)]

/-- Root caller expecting a `u64` return from a `fn(u32) -> u32` closure function. -/
def cfMrBadRetCaller : Gen.Function :=
  mkMrFn [(localName 0, u64MrTy), (localName 1, u32MrTy), (localName 2, thinRawPtrTy)] [localName 1] (localName 0)
    [(bbName 0, cfBlk [.Assign (cfLc 2) (cfFnPtrC 1)] (cfCall (cfLd 2) [cfLd 1] 0 1 .Rust)), cfLoopBb 1]

/-- MiniRust transmuted return signature: a `u64` return destination for `fn(u32) -> u32`. -/
def cfMrBadRetMach : Mach :=
  cfMrMach [cfMrBadRetCaller, cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))]
    [(cfU 8, 8), (cfU32B 5, 4), (cfU 8, 8)]

/-- **Callee-directed environment prepend for all three receiver modes
(kernel-checked on the verbatim closure bodies).** One `stepMirFn` step of an
indirect `fn(u32) -> u32` call on `5` enters the closure body with four locals
on a call stack of depth `1`, `_2 = 5`, and `_1` bound to
* `Fn` (`&{closure}`): the scalar `⟨1, 8⟩` (code `118`),
* `FnMut` (`&mut {closure}`): the scalar `⟨1, 8⟩` (code `118`),
* `FnOnce` (`{closure}` by value): the empty aggregate (code `1`).
The `FnPtrEntry` carries no closure flag: the dispatch is decided by the
linked body alone. -/
theorem cf_env_prepend_three_receiver_modes_witness :
    cfEntryObs (cfPtrCaller cfFnU32)
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32) = some (118, 5, 4, 1) ∧
    cfEntryObs (cfPtrCaller cfFnU32)
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_mut_kind_closure_0
        "closure_matrix::fn_mut_kind::{closure#0}" cfFnU32) = some (118, 5, 4, 1) ∧
    cfEntryObs (cfPtrCaller cfFnU32)
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_once_kind_closure_0
        "closure_matrix::fn_once_kind::{closure#0}" cfFnU32) = some (1, 5, 4, 1) ∧
    cfEnvCode (synthesizeClosureEnvArg .sharedRef 8) = 118 ∧ cfEnvCode (synthesizeClosureEnvArg .mutRef 8) = 118 ∧
    cfEnvCode (synthesizeClosureEnvArg .byValue 8) = 1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩

/-- **Fail-closed coercion witnesses** (real `evalRvalue`, verbatim closure
bodies linked). Positive controls: `ClosureFnPointer(Safe)` to `fn(u32) -> u32`
and `ClosureFnPointer(Unsafe)` to `unsafe fn(u32) -> u32` succeed. Negatives:
a closure capturing a `u32` (`.ub`), a closure capturing the zero-sized `()`
(`.ub`, with a non-empty and with an empty aggregate value), a `Safe` tag to
an `unsafe fn` target and an `Unsafe` tag to a safe target (`.ub`),
`extern "C"` (`.ub`), a transmuted parameter type (`.ub`), a generic closure
under `R1` (`.unsupported`, never `.ub`), and the unrecognized
`"ClosureFnPointer(Normal)"` spelling (`.unsupported`). -/
theorem cf_coercion_fail_closed_witness :
    cfCoerce "ClosureFnPointer(Safe)" cfSharedClo (.aggregate 0 []) cfFnU32 [cfFx_fn_shared_closure_0] = .ok ∧
    cfCoerce "ClosureFnPointer(Unsafe)" cfSharedClo (.aggregate 0 []) (.fnPtr [cfU32K] cfU32K .unsafe_ .rust)
      [cfFx_fn_shared_closure_0] = .ok ∧
    cfShapeTag (calleeOwnClosureShape? cfFx_capturing_direct_closure_0) = 4 ∧
    cfShapeTag (calleeOwnClosureShape? cfFx_capturing_direct_closure_1) = 4 ∧
    cfCoerce "ClosureFnPointer(Safe)" cfCapClo (.aggregate 0 [cfU32V 7]) cfFnU32
      [cfFx_capturing_direct_closure_0] = .ub ∧
    cfCoerce "ClosureFnPointer(Safe)" cfCapZstClo (.aggregate 0 [.unit]) cfFnU32
      [cfFx_capturing_direct_closure_1] = .ub ∧
    cfCoerce "ClosureFnPointer(Safe)" cfCapZstClo (.aggregate 0 []) cfFnU32
      [cfFx_capturing_direct_closure_1] = .ub ∧
    cfCoerce "ClosureFnPointer(Safe)" cfSharedClo (.aggregate 0 []) (.fnPtr [cfU32K] cfU32K .unsafe_ .rust)
      [cfFx_fn_shared_closure_0] = .ub ∧
    cfCoerce "ClosureFnPointer(Unsafe)" cfSharedClo (.aggregate 0 []) cfFnU32 [cfFx_fn_shared_closure_0] = .ub ∧
    cfCoerce "ClosureFnPointer(Safe)" cfSharedClo (.aggregate 0 []) (.fnPtr [cfU32K] cfU32K .safe .c)
      [cfFx_fn_shared_closure_0] = .ub ∧
    cfCoerce "ClosureFnPointer(Safe)" cfSharedClo (.aggregate 0 []) (.fnPtr [.uint .u64] cfU32K .safe .rust)
      [cfFx_fn_shared_closure_0] = .ub ∧
    cfFx_generic_closure_closure_0.typeParamCount = 1 ∧
    cfCoerce "ClosureFnPointer(Safe)" (.closure cfGenericPath []) (.aggregate 0 []) cfFnU32
      [cfFx_generic_closure_closure_0] = .unsupported ∧
    cfCoerce "ClosureFnPointer(Normal)" cfSharedClo (.aggregate 0 []) cfFnU32 [cfFx_fn_shared_closure_0] =
      .unsupported :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, rfl, by decide +kernel, by decide +kernel⟩

/-- **Fail-closed indirect-call witnesses** (real `stepMirFn`, verbatim closure
bodies linked) with their MiniRust counterparts on `Mach` and `MachTB`.
* Positive control: a pointer whose `FnPtrEntry` merely names the closure
  (no closure flag) dispatches, `22`.
* A pointer to the closure capturing a `u32`, and to the closure capturing the
  zero-sized `()`, is `.ub` (C10).
* A forged `(N + 1)`-argument pointer passing the environment explicitly is
  `.ub` for the non-capturing, the `u32`-capturing, and the `()`-capturing
  closure (C10); MiniRust: `"number of arguments does not agree"`.
* A transmuted signature (`fn(u64) -> u32`) is `.ub`; MiniRust:
  `"argument types are not compatible"`.
* An `extern "C"` pointer is `.ub`; MiniRust:
  `"calling conventions are not the same"`.
* The generic closure of the verbatim `call_generic` capture is
  `.unsupported` under `R1` (C5), never `.ub`.
* A direct call passing `&_env` explicitly dispatches, `22` (C11), and the
  verbatim `direct_closure_call` capture (a direct `Fn::call` trait call)
  stays an external call. -/
theorem cf_indirect_call_fail_closed_three_way_witness :
    cfRun (cfPtrCaller cfFnU32) 16
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32) = .scalar 22 4 ∧
    cfRun (cfPtrCaller cfFnU32) 16
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_capturing_direct_closure_0 cfCapPath cfFnU32) = .ub ∧
    cfRun (cfPtrCaller cfFnU32) 16
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_capturing_direct_closure_1 cfCapZstPath cfFnU32) = .ub ∧
    cfRun (cfEnvPtrCaller (.fnPtr [.ref .not cfSharedClo, cfU32K] cfU32K .safe .rust) (.ref .not cfSharedClo)) 16
      (cfEnvPtrCallState cfSharedClo cfFx_fn_shared_closure_0 cfSharedPath) = .ub ∧
    cfRun (cfEnvPtrCaller (.fnPtr [.ref .not cfCapClo, cfU32K] cfU32K .safe .rust) (.ref .not cfCapClo)) 16
      (cfEnvPtrCallState cfCapClo cfFx_capturing_direct_closure_0 cfCapPath) = .ub ∧
    cfRun (cfEnvPtrCaller (.fnPtr [.ref .not cfCapZstClo, cfU32K] cfU32K .safe .rust) (.ref .not cfCapZstClo)) 16
      (cfEnvPtrCallState cfCapZstClo cfFx_capturing_direct_closure_1 cfCapZstPath) = .ub ∧
    CfMrUb 4 cfMrForgedArityMach "call ABI violation: number of arguments does not agree" ∧
    cfRun (cfPtrCaller (.fnPtr [.uint .u64] cfU32K .safe .rust) (.uint .u64)) 16
      (cfPtrCallState (.fnPtr [.uint .u64] cfU32K .safe .rust) (.scalar ⟨5, 8⟩) cfFx_fn_shared_closure_0
        cfSharedPath (.fnPtr [.uint .u64] cfU32K .safe .rust) (.uint .u64)) = .ub ∧
    CfMrUb 4 cfMrBadSigMach "call ABI violation: argument types are not compatible" ∧
    cfRun (cfPtrCaller (.fnPtr [cfU32K] (.uint .u64) .safe .rust)) 16
      (cfPtrCallState (.fnPtr [cfU32K] (.uint .u64) .safe .rust) (cfU32V 5) cfFx_fn_shared_closure_0
        cfSharedPath (.fnPtr [cfU32K] (.uint .u64) .safe .rust)) = .ub ∧
    CfMrUb 4 cfMrBadRetMach "call ABI violation: return types are not compatible" ∧
    cfRun (cfPtrCaller (.fnPtr [cfU32K] cfU32K .safe .c)) 16
      (cfPtrCallState (.fnPtr [cfU32K] cfU32K .safe .c) (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath
        (.fnPtr [cfU32K] cfU32K .safe .c)) = .ub ∧
    CfMrUb 4 cfMrExternCMach "call ABI violation: calling conventions are not the same" ∧
    cfRun cfFx_call_generic 64
      (cfInit cfFx_call_generic [cfU32V 77] [cfFx_generic_closure, cfFx_generic_closure_closure_0]) =
      .unsupported ∧
    cfRun (cfDirectEnvCaller cfSharedPath (.ref .not cfSharedClo)) 16
      (cfInit (cfDirectEnvCaller cfSharedPath (.ref .not cfSharedClo)) [cfEnvScalar, cfU32V 5]
        [cfFx_fn_shared_closure_0]) = .scalar 22 4 ∧
    cfRun cfFx_direct_closure_call 64
      (cfInit cfFx_direct_closure_call [cfU32V 5] [cfFx_direct_closure_call_closure_0]) =
      .ext "core::ops::Fn::call" :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, cfMrUb_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel,
   cfMrUb_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel,
   cfMrUb_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel,
   cfMrUb_of_decide (by decide +kernel) (by decide +kernel), by decide +kernel, by decide +kernel,
   by decide +kernel⟩

/-- **The universal indirect-call law instantiated on a verbatim `Fn` closure
body (non-vacuity).** All premises of `closure_indirect_call_prepends_env` hold
for the pointer call of `cfPtrCallState`, so the real `stepMirFn` step IS the
callee-directed frame push with the synthesized environment prepended. -/
theorem closure_indirect_call_law_instance_fn :
    stepMirFn (cfPtrCaller cfFnU32)
        (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32) =
      MirStepNode.step (pushCalleeFrame
        (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32) (cfPtrCaller cfFnU32)
        (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32).frame.locals
        (locPlace 0) 1 cfFx_fn_shared_closure_0
        (synthesizeClosureEnvArg .sharedRef (layoutPointerBytes cfFx_fn_shared_closure_0.layouts) :: [cfU32V 5])
        .continue_) :=
  (closure_indirect_call_prepends_env
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32) (cfPtrCaller cfFnU32)
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    { defPath := cfSharedPath, typeArgs := [], fnSig := some cfFnU32, isIndirect := true }
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32).frame.locals
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32).frame.locals
    [cfU32V 5] cfFx_fn_shared_closure_0 .sharedRef rfl rfl rfl rfl (cfShapeTag_inj (by decide +kernel)) rfl).1

/-- **The universal indirect-call law instantiated on a verbatim `FnMut` closure
body (non-vacuity).** -/
theorem closure_indirect_call_law_instance_fnMut :
    let dp := "closure_matrix::fn_mut_kind::{closure#0}"
    let st := cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_mut_kind_closure_0 dp cfFnU32
    stepMirFn (cfPtrCaller cfFnU32) st =
      MirStepNode.step (pushCalleeFrame st (cfPtrCaller cfFnU32) st.frame.locals (locPlace 0) 1
        cfFx_fn_mut_kind_closure_0
        (synthesizeClosureEnvArg .mutRef (layoutPointerBytes cfFx_fn_mut_kind_closure_0.layouts) :: [cfU32V 5])
        .continue_) :=
  (closure_indirect_call_prepends_env
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_mut_kind_closure_0 "closure_matrix::fn_mut_kind::{closure#0}" cfFnU32)
    (cfPtrCaller cfFnU32) (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    { defPath := "closure_matrix::fn_mut_kind::{closure#0}", typeArgs := [], fnSig := some cfFnU32, isIndirect := true }
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_mut_kind_closure_0 "closure_matrix::fn_mut_kind::{closure#0}" cfFnU32).frame.locals
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_mut_kind_closure_0 "closure_matrix::fn_mut_kind::{closure#0}" cfFnU32).frame.locals
    [cfU32V 5] cfFx_fn_mut_kind_closure_0 .mutRef rfl rfl rfl rfl (cfShapeTag_inj (by decide +kernel)) rfl).1

/-- **The universal indirect-call law instantiated on a verbatim `FnOnce` closure
body (non-vacuity).** -/
theorem closure_indirect_call_law_instance_fnOnce :
    let dp := "closure_matrix::fn_once_kind::{closure#0}"
    let st := cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_once_kind_closure_0 dp cfFnU32
    stepMirFn (cfPtrCaller cfFnU32) st =
      MirStepNode.step (pushCalleeFrame st (cfPtrCaller cfFnU32) st.frame.locals (locPlace 0) 1
        cfFx_fn_once_kind_closure_0
        (synthesizeClosureEnvArg .byValue (layoutPointerBytes cfFx_fn_once_kind_closure_0.layouts) :: [cfU32V 5])
        .continue_) :=
  (closure_indirect_call_prepends_env
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_once_kind_closure_0 "closure_matrix::fn_once_kind::{closure#0}" cfFnU32)
    (cfPtrCaller cfFnU32) (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    { defPath := "closure_matrix::fn_once_kind::{closure#0}", typeArgs := [], fnSig := some cfFnU32, isIndirect := true }
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_once_kind_closure_0 "closure_matrix::fn_once_kind::{closure#0}" cfFnU32).frame.locals
    (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_once_kind_closure_0 "closure_matrix::fn_once_kind::{closure#0}" cfFnU32).frame.locals
    [cfU32V 5] cfFx_fn_once_kind_closure_0 .byValue rfl rfl rfl rfl (cfShapeTag_inj (by decide +kernel)) rfl).1

/-- **`ClosureFnPtrEntryRel` instantiated on the verbatim `Fn` closure body and
the reference machine, on `Mach` AND `MachTB` (non-vacuity).** The Trusted
pointer at `65536` (an `FnPtrEntry` without any closure flag) and MiniRust
function pointer `fn_ptrs[1]` at address `8192` are related for the Trusted
body `fn_shared::{closure#0}` (`argCount = 2`) and the MiniRust function of
arity `1`. -/
theorem closureFnPtrEntryRel_instance_mach_and_tb :
    ClosureFnPtrEntryRel
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32).memory
      { allocId := 65536, offsetBytes := 0 }
      (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [5]) (fnName 1) 8192 (some (⟨4⟩, ()))
      cfFx_fn_shared_closure_0 .sharedRef (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) 1 ∧
    (∃ provTB, ClosureFnPtrEntryRel
      (cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32).memory
      { allocId := 65536, offsetBytes := 0 }
      (liftMachToTB (cfMrIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [5])) (fnName 1) 8192
      provTB cfFx_fn_shared_closure_0 .sharedRef (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) 1) :=
  ⟨{ entry := ⟨rfl, rfl, by decide, rfl⟩, fnEntry := ⟨_, rfl, rfl, rfl⟩, linked := rfl,
     shape := cfShapeTag_inj (by decide +kernel), nonGeneric := rfl, trustedArity := rfl, mrResolve := rfl,
     mrArity := rfl, mrConv := rfl },
   ⟨_, { entry := ⟨rfl, rfl, by decide, rfl⟩, fnEntry := ⟨_, rfl, rfl, rfl⟩, linked := rfl,
         shape := cfShapeTag_inj (by decide +kernel), nonGeneric := rfl, trustedArity := rfl, mrResolve := rfl,
         mrArity := rfl, mrConv := rfl }⟩⟩

private theorem storageDeadM_func_eq {M : Type} [Gen.Memory M] [MemoryOps M]
    {fr fr' : StackFrame M} {cm cm' : ConcurrentMemory M} {l : LocalName}
    (h : storageDeadM fr cm l = .ok (fr', cm')) : fr'.func = fr.func := by
  unfold storageDeadM at h
  cases h0 : mapIndex fr.func.locals l "self.func.locals[local]" with
  | error e => simp only [h0, bind, Except.bind] at h; cases h
  | ok ty =>
    simp only [h0, bind, Except.bind] at h
    cases h1 : «Type».layout ty with
    | error e => simp only [h1] at h; cases h
    | ok ly =>
      simp only [h1] at h
      cases h2 : LayoutStrategy.expect_size ly "WF ensures all locals are sized" with
      | error e => simp only [h2] at h; cases h
      | ok sz =>
        simp only [h2] at h
        cases h3 : LayoutStrategy.expect_align ly "WF ensures all locals are sized" with
        | error e => simp only [h3] at h; cases h
        | ok al =>
          simp only [h3] at h
          cases h4 : mapRemove fr.locals l with
          | mk rem locals =>
            simp only [h4] at h
            cases rem with
            | none =>
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1]
            | some ptr =>
              cases h5 : ConcurrentMemory.deallocate cm ptr .Stack sz al with
              | error e => simp only [h5] at h; cases h
              | ok cm2 =>
                simp only [h5, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.1]

private theorem storageLiveM_func_eq {M : Type} [Gen.Memory M] [MemoryOps M]
    {fr fr' : StackFrame M} {cm cm' : ConcurrentMemory M} {l : LocalName}
    (h : storageLiveM fr cm l = .ok (fr', cm')) : fr'.func = fr.func := by
  unfold storageLiveM at h
  cases h1 : storageDeadM fr cm l with
  | error e => simp only [h1, bind, Except.bind] at h; cases h
  | ok p1 =>
    simp only [h1, bind, Except.bind] at h
    cases h2 : mapIndex p1.1.func.locals l "self.func.locals[local]" with
    | error e => simp only [h2] at h; cases h
    | ok ty =>
      simp only [h2] at h
      cases h3 : «Type».layout ty with
      | error e => simp only [h3] at h; cases h
      | ok ly =>
        simp only [h3] at h
        cases h4 : LayoutStrategy.expect_size ly "WF ensures all locals are sized" with
        | error e => simp only [h4] at h; cases h
        | ok sz =>
          simp only [h4] at h
          cases h5 : LayoutStrategy.expect_align ly "WF ensures all locals are sized" with
          | error e => simp only [h5] at h; cases h
          | ok al =>
            simp only [h5] at h
            cases h6 : ConcurrentMemory.allocate p1.2 .Stack sz al with
            | error e => simp only [h6] at h; cases h
            | ok p3 =>
              simp only [h6, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1]; dsimp only; exact storageDeadM_func_eq h1

private theorem allocFrameArgsM_func_eq {M : Type} [Gen.Memory M] [MemoryOps M]
    {fr fr' : StackFrame M} {cm cm' : ConcurrentMemory M} {args : List LocalName}
    (h : allocFrameArgsM fr cm args = .ok (fr', cm')) : fr'.func = fr.func := by
  induction args generalizing fr cm with
  | nil =>
    simp only [allocFrameArgsM, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact congrArg StackFrame.func h.1.symm
  | cons a rest ih =>
    simp only [allocFrameArgsM, bind, Except.bind] at h
    cases h1 : storageLiveM fr cm a with
    | error e => simp only [h1] at h; cases h
    | ok p1 =>
      simp only [h1] at h
      exact (ih h).trans (storageLiveM_func_eq h1)

/-- **Non-vacuity instantiation of the coupled two-sided indirect call law
`closure_indirect_call_correspondence_M` on BOTH `Mach` and `MachTB`**:
all premises of `closure_indirect_call_correspondence_M` hold simultaneously on
the verbatim `fn_shared::{closure#0}` Trusted state and `cfMrIndirectMach`
reference machine (both `BM` and `TBM`). -/
theorem closure_indirect_call_correspondence_instance_mach_and_tb :
    let s := cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32
    let mBM := cfMrIndirectMach (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [5]
    let mTB := liftMachToTB mBM
    let fn := cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))
    (∃ f2 cm2,
      evalTerminator s
          { kind := .call (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) (some 1) .continue_, span := "ptr_call" }
          (some (cfPtrCaller cfFnU32)) =
        MirStepNode.step (pushCalleeFrame s (cfPtrCaller cfFnU32) s.frame.locals (locPlace 0) 1
          cfFx_fn_shared_closure_0
          (synthesizeClosureEnvArg .sharedRef (layoutPointerBytes cfFx_fn_shared_closure_0.layouts) :: [cfU32V 5])
          .continue_) ∧
      createFrameM mBM fn .BottomOfStack .Rust u32MrTy [(.Int 5, u32MrTy)] =
        (initFrameArgsM { mBM with mem := cm2 } f2 fn.args [(.Int 5, u32MrTy)]).map (fun m' => (f2, m'))) ∧
    (∃ f2 cm2,
      createFrameM mTB fn .BottomOfStack .Rust u32MrTy [(.Int 5, u32MrTy)] =
        (initFrameArgsM { mTB with mem := cm2 } f2 fn.args [(.Int 5, u32MrTy)]).map (fun m' => (f2, m'))) := by
  dsimp only
  let s := cfPtrCallState cfFnU32 (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath cfFnU32
  let fn := cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))
  let mBM := cfMrIndirectMach fn [5]
  let mTB := liftMachToTB mBM
  obtain ⟨hRelBM, provTB, hRelTB⟩ := closureFnPtrEntryRel_instance_mach_and_tb
  have hCompatSite : ∀ e, lookupFnPtr s.memory.fnPtrs (65536 : Nat) = some e →
      fnEntryCompatibleWithCallSite e (length [MirAst.Operand.copy (locPlace 2)])
        (operandTy (cfPtrCaller cfFnU32).localDecls (cfPtrCaller cfFnU32).layouts (.copy (locPlace 1))) = true := by
    intro e he
    have : e = cfEntry cfSharedPath cfFnU32 := by
      have h' : some (cfEntry cfSharedPath cfFnU32) = some e := he
      exact (Option.some.inj h').symm
    subst this
    rfl
  have hCompatTarget : ∀ e, lookupFnPtr s.memory.fnPtrs (65536 : Nat) = some e →
      checkClosureTargetCompatible
        ({ defPath := cfFx_fn_shared_closure_0.defPath, typeArgs := [], fnSig := e.fnSig, isIndirect := true } :
          ResolvedCallTarget) cfFx_fn_shared_closure_0 1 = true := by
    intro e he
    have : e = cfEntry cfSharedPath cfFnU32 := by
      have h' : some (cfEntry cfSharedPath cfFnU32) = some e := he
      exact (Option.some.inj h').symm
    subst this
    rfl
  let initFrBM : StackFrame BM :=
    { func := fn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
      next_block := fn.start, next_stmt := 0, extra := MemoryOps.new_call }
  let initFrTB : StackFrame TBM :=
    { func := fn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
      next_block := fn.start, next_stmt := 0, extra := MemoryOps.new_call }
  have hBMInit : ∃ f1 cm1 f2 cm2,
      storageLiveM initFrBM mBM.mem fn.ret = .ok (f1, cm1) ∧
      allocFrameArgsM f1 cm1 fn.args = .ok (f2, cm2) := by
    have hOk : (do
        let (f1, cm1) ← storageLiveM initFrBM mBM.mem fn.ret
        let _ ← allocFrameArgsM f1 cm1 fn.args
        pure true).toOption = some true := by decide +kernel
    cases h1 : storageLiveM initFrBM mBM.mem fn.ret with
    | error e => simp only [h1, bind, Except.bind, Except.toOption] at hOk; cases hOk
    | ok p1 =>
      cases h2 : allocFrameArgsM p1.1 p1.2 fn.args with
      | error e => simp only [h1, h2, bind, Except.bind, Except.toOption] at hOk; cases hOk
      | ok p2 => exact ⟨p1.1, p1.2, p2.1, p2.2, rfl, h2⟩
  have hTBInit : ∃ f1 cm1 f2 cm2,
      storageLiveM initFrTB mTB.mem fn.ret = .ok (f1, cm1) ∧
      allocFrameArgsM f1 cm1 fn.args = .ok (f2, cm2) := by
    have hOk : (do
        let (f1, cm1) ← storageLiveM initFrTB mTB.mem fn.ret
        let _ ← allocFrameArgsM f1 cm1 fn.args
        pure true).toOption = some true := by decide +kernel
    cases h1 : storageLiveM initFrTB mTB.mem fn.ret with
    | error e => simp only [h1, bind, Except.bind, Except.toOption] at hOk; cases hOk
    | ok p1 =>
      cases h2 : allocFrameArgsM p1.1 p1.2 fn.args with
      | error e => simp only [h1, h2, bind, Except.bind, Except.toOption] at hOk; cases hOk
      | ok p2 => exact ⟨p1.1, p1.2, p2.1, p2.2, rfl, h2⟩
  obtain ⟨f1BM, cm1BM, f2BM, cm2BM, hSLBM, hAABM⟩ := hBMInit
  obtain ⟨f1TB, cm1TB, f2TB, cm2TB, hSLTB, hAATB⟩ := hTBInit
  have hLawBM := closure_indirect_call_correspondence_M (M := BM) s (cfPtrCaller cfFnU32)
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    s.frame.locals s.frame.locals [cfU32V 5] hRelBM rfl rfl hCompatSite rfl rfl
    .BottomOfStack u32MrTy [(.Int 5, u32MrTy)] f1BM f2BM cm1BM cm2BM u32MrTy hSLBM hAABM
    (by
      have hEq := allocFrameArgsM_func_eq hAABM
      have hEq1 := storageLiveM_func_eq hSLBM
      rw [hEq, hEq1]; rfl) rfl rfl
  have hLawTB := closure_indirect_call_correspondence_M (M := TBM) s (cfPtrCaller cfFnU32)
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    s.frame.locals s.frame.locals [cfU32V 5] hRelTB rfl rfl hCompatSite rfl rfl
    .BottomOfStack u32MrTy [(.Int 5, u32MrTy)] f1TB f2TB cm1TB cm2TB u32MrTy hSLTB hAATB
    (by
      have hEq := allocFrameArgsM_func_eq hAATB
      have hEq1 := storageLiveM_func_eq hSLTB
      rw [hEq, hEq1]; rfl) rfl rfl
  exact ⟨⟨f2BM, cm2BM, hLawBM.2.2.1 rfl hCompatTarget⟩,
         ⟨f2TB, cm2TB, (hLawTB.2.2.1 rfl hCompatTarget).2⟩⟩

/-- **Non-vacuity instantiations of `ClosureFnSigRel` and
`closure_typed_sig_call_correspondence_M` on verbatim captured closure bodies
and reference MiniRust functions (`Mach` & `MachTB`)**:
1. `ClosureFnSigRel` holds for all five closure arities/kinds:
   `fn_shared` (`fn(u32) -> u32`), `fn_mut_kind` (`fn(u32) -> u32`),
   `fn_once_kind` (`fn(u32) -> u32`), `zero_arg` (`fn() -> u32`), and
   `two_arg` (`fn(u32, u32) -> u32`);
2. `closure_typed_sig_call_correspondence_M` instantiates on BOTH `Mach` and
   `MachTB` for return-type transmutation (`fn(u32) -> u64`) AND argument-type
   transmutation (`fn(u64) -> u32`), witnessing simultaneous UB on Trusted and
   MiniRust. -/
theorem closure_typed_sig_instances_mach_and_tb :
    ClosureFnSigRel cfFx_fn_shared_closure_0 (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))) [.uint .u32] (.uint .u32) u32MrTy ∧
    ClosureFnSigRel cfFx_fn_mut_kind_closure_0 (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 2))) [.uint .u32] (.uint .u32) u32MrTy ∧
    ClosureFnSigRel cfFx_fn_once_kind_closure_0 (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 3))) [.uint .u32] (.uint .u32) u32MrTy ∧
    ClosureFnSigRel cfFx_zero_arg_closure_0 (cfMrLeafFn 0 (cfU32 7)) [] (.uint .u32) u32MrTy ∧
    ClosureFnSigRel cfFx_two_arg_closure_0 (cfMrLeafFn 2 (cfBin .BitXor (cfLd 1) (cfLd 2))) [.uint .u32, .uint .u32] (.uint .u32) u32MrTy ∧
    (let fn := cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))
     let mBM := cfMrIndirectMach fn [5]
     let mTB := liftMachToTB mBM
     let sBadRet := cfPtrCallState (.fnPtr [cfU32K] (.uint .u64) .safe .rust) (cfU32V 5)
       cfFx_fn_shared_closure_0 cfSharedPath (.fnPtr [cfU32K] (.uint .u64) .safe .rust)
     let sBadArg := cfPtrCallState (.fnPtr [.uint .u64] cfU32K .safe .rust) (.scalar ⟨5, 8⟩)
       cfFx_fn_shared_closure_0 cfSharedPath (.fnPtr [.uint .u64] cfU32K .safe .rust) (.uint .u64)
     evalTerminator sBadRet
         { kind := .call (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) (some 1) .continue_, span := "ptr_call" }
         (some (cfPtrCaller (.fnPtr [cfU32K] (.uint .u64) .safe .rust))) = MirStepNode.fail .ub ∧
     createFrameM mBM fn .BottomOfStack .Rust u64MrTy [(.Int 5, u32MrTy)] =
       .error (.ub "call ABI violation: return types are not compatible") ∧
     createFrameM mTB fn .BottomOfStack .Rust u64MrTy [(.Int 5, u32MrTy)] =
       .error (.ub "call ABI violation: return types are not compatible") ∧
     evalTerminator sBadArg
         { kind := .call (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) (some 1) .continue_, span := "ptr_call" }
         (some (cfPtrCaller (.fnPtr [.uint .u64] cfU32K .safe .rust) (.uint .u64))) = MirStepNode.fail .ub ∧
     createFrameM mBM fn .BottomOfStack .Rust u32MrTy [(.Int 5, u64MrTy)] =
       .error (.ub "call ABI violation: argument types are not compatible") ∧
     createFrameM mTB fn .BottomOfStack .Rust u32MrTy [(.Int 5, u64MrTy)] =
       .error (.ub "call ABI violation: argument types are not compatible")) := by
  have hSigShared : ClosureFnSigRel cfFx_fn_shared_closure_0 (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17)))
      [.uint .u32] (.uint .u32) u32MrTy :=
    { decls := ⟨_, _, _, rfl, rfl, rfl, rfl⟩, retTranslate := rfl, mrRetLookup := rfl,
      argsRel := ⟨⟨u32MrTy, rfl, rfl⟩, trivial⟩ }
  have hSigMut : ClosureFnSigRel cfFx_fn_mut_kind_closure_0 (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 2)))
      [.uint .u32] (.uint .u32) u32MrTy :=
    { decls := ⟨_, _, _, rfl, rfl, rfl, rfl⟩, retTranslate := rfl, mrRetLookup := rfl,
      argsRel := ⟨⟨u32MrTy, rfl, rfl⟩, trivial⟩ }
  have hSigOnce : ClosureFnSigRel cfFx_fn_once_kind_closure_0 (cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 3)))
      [.uint .u32] (.uint .u32) u32MrTy :=
    { decls := ⟨_, _, _, rfl, rfl, rfl, rfl⟩, retTranslate := rfl, mrRetLookup := rfl,
      argsRel := ⟨⟨u32MrTy, rfl, rfl⟩, trivial⟩ }
  have hSigZero : ClosureFnSigRel cfFx_zero_arg_closure_0 (cfMrLeafFn 0 (cfU32 7)) [] (.uint .u32) u32MrTy :=
    { decls := ⟨_, _, _, rfl, rfl, rfl, rfl⟩, retTranslate := rfl, mrRetLookup := rfl,
      argsRel := trivial }
  have hSigTwo : ClosureFnSigRel cfFx_two_arg_closure_0 (cfMrLeafFn 2 (cfBin .BitXor (cfLd 1) (cfLd 2)))
      [.uint .u32, .uint .u32] (.uint .u32) u32MrTy :=
    { decls := ⟨_, _, _, rfl, rfl, rfl, rfl⟩, retTranslate := rfl, mrRetLookup := rfl,
      argsRel := ⟨⟨u32MrTy, rfl, rfl⟩, ⟨u32MrTy, rfl, rfl⟩, trivial⟩ }
  refine ⟨hSigShared, hSigMut, hSigOnce, hSigZero, hSigTwo, ?_⟩
  dsimp only
  let fn := cfMrLeafFn 1 (cfBin .Add (cfLd 1) (cfU32 17))
  let mBM := cfMrIndirectMach fn [5]
  let mTB := liftMachToTB mBM
  let initFrBM : StackFrame BM :=
    { func := fn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
      next_block := fn.start, next_stmt := 0, extra := MemoryOps.new_call }
  let initFrTB : StackFrame TBM :=
    { func := fn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
      next_block := fn.start, next_stmt := 0, extra := MemoryOps.new_call }
  have hBMInit : ∃ f1 cm1 f2 cm2,
      storageLiveM initFrBM mBM.mem fn.ret = .ok (f1, cm1) ∧
      allocFrameArgsM f1 cm1 fn.args = .ok (f2, cm2) := by
    have hOk : (do
        let (f1, cm1) ← storageLiveM initFrBM mBM.mem fn.ret
        let _ ← allocFrameArgsM f1 cm1 fn.args
        pure true).toOption = some true := by decide +kernel
    cases h1 : storageLiveM initFrBM mBM.mem fn.ret with
    | error e => simp only [h1, bind, Except.bind, Except.toOption] at hOk; cases hOk
    | ok p1 =>
      cases h2 : allocFrameArgsM p1.1 p1.2 fn.args with
      | error e => simp only [h1, h2, bind, Except.bind, Except.toOption] at hOk; cases hOk
      | ok p2 => exact ⟨p1.1, p1.2, p2.1, p2.2, rfl, h2⟩
  have hTBInit : ∃ f1 cm1 f2 cm2,
      storageLiveM initFrTB mTB.mem fn.ret = .ok (f1, cm1) ∧
      allocFrameArgsM f1 cm1 fn.args = .ok (f2, cm2) := by
    have hOk : (do
        let (f1, cm1) ← storageLiveM initFrTB mTB.mem fn.ret
        let _ ← allocFrameArgsM f1 cm1 fn.args
        pure true).toOption = some true := by decide +kernel
    cases h1 : storageLiveM initFrTB mTB.mem fn.ret with
    | error e => simp only [h1, bind, Except.bind, Except.toOption] at hOk; cases hOk
    | ok p1 =>
      cases h2 : allocFrameArgsM p1.1 p1.2 fn.args with
      | error e => simp only [h1, h2, bind, Except.bind, Except.toOption] at hOk; cases hOk
      | ok p2 => exact ⟨p1.1, p1.2, p2.1, p2.2, rfl, h2⟩
  obtain ⟨f1BM, cm1BM, f2BM, cm2BM, hSLBM, hAABM⟩ := hBMInit
  obtain ⟨f1TB, cm1TB, f2TB, cm2TB, hSLTB, hAATB⟩ := hTBInit
  have hF2BM : f2BM.func = fn := (allocFrameArgsM_func_eq hAABM).trans (storageLiveM_func_eq hSLBM)
  have hF2TB : f2TB.func = fn := (allocFrameArgsM_func_eq hAATB).trans (storageLiveM_func_eq hSLTB)
  let sigRet : RigidTy := .fnPtr [cfU32K] (.uint .u64) .safe .rust
  let sBadRet := cfPtrCallState sigRet (cfU32V 5) cfFx_fn_shared_closure_0 cfSharedPath sigRet
  let sigArg : RigidTy := .fnPtr [.uint .u64] cfU32K .safe .rust
  let sBadArg := cfPtrCallState sigArg (.scalar ⟨5, 8⟩) cfFx_fn_shared_closure_0 cfSharedPath sigArg (.uint .u64)
  obtain ⟨hBaseBM, provTB, hBaseTB⟩ := closureFnPtrEntryRel_instance_mach_and_tb
  have hRelRetBM : ClosureFnPtrEntryRel sBadRet.memory { allocId := 65536, offsetBytes := 0 }
      mBM (fnName 1) 8192 (some (⟨4⟩, ())) cfFx_fn_shared_closure_0 .sharedRef fn 1 :=
    { entry := ⟨rfl, rfl, by decide, hBaseBM.entry.2.2.2⟩, fnEntry := ⟨_, rfl, rfl, rfl⟩, linked := rfl,
      shape := hBaseBM.shape, nonGeneric := rfl, trustedArity := rfl,
      mrResolve := hBaseBM.mrResolve, mrArity := rfl, mrConv := rfl }
  have hRelRetTB : ClosureFnPtrEntryRel sBadRet.memory { allocId := 65536, offsetBytes := 0 }
      mTB (fnName 1) 8192 provTB cfFx_fn_shared_closure_0 .sharedRef fn 1 :=
    { entry := ⟨rfl, rfl, by decide, hBaseTB.entry.2.2.2⟩, fnEntry := ⟨_, rfl, rfl, rfl⟩, linked := rfl,
      shape := hBaseTB.shape, nonGeneric := rfl, trustedArity := rfl,
      mrResolve := hBaseTB.mrResolve, mrArity := rfl, mrConv := rfl }
  have hRelArgBM : ClosureFnPtrEntryRel sBadArg.memory { allocId := 65536, offsetBytes := 0 }
      mBM (fnName 1) 8192 (some (⟨4⟩, ())) cfFx_fn_shared_closure_0 .sharedRef fn 1 :=
    { entry := ⟨rfl, rfl, by decide, hBaseBM.entry.2.2.2⟩, fnEntry := ⟨_, rfl, rfl, rfl⟩, linked := rfl,
      shape := hBaseBM.shape, nonGeneric := rfl, trustedArity := rfl,
      mrResolve := hBaseBM.mrResolve, mrArity := rfl, mrConv := rfl }
  have hRelArgTB : ClosureFnPtrEntryRel sBadArg.memory { allocId := 65536, offsetBytes := 0 }
      mTB (fnName 1) 8192 provTB cfFx_fn_shared_closure_0 .sharedRef fn 1 :=
    { entry := ⟨rfl, rfl, by decide, hBaseTB.entry.2.2.2⟩, fnEntry := ⟨_, rfl, rfl, rfl⟩, linked := rfl,
      shape := hBaseTB.shape, nonGeneric := rfl, trustedArity := rfl,
      mrResolve := hBaseTB.mrResolve, mrArity := rfl, mrConv := rfl }
  have hLawRetBM := closure_typed_sig_call_correspondence_M (M := BM) sBadRet (cfPtrCaller sigRet)
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    sBadRet.frame.locals sBadRet.frame.locals [cfU32V 5] hRelRetBM hSigShared rfl rfl rfl rfl
    .BottomOfStack f1BM f2BM cm1BM cm2BM hSLBM hAABM hF2BM
  have hLawRetTB := closure_typed_sig_call_correspondence_M (M := TBM) sBadRet (cfPtrCaller sigRet)
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    sBadRet.frame.locals sBadRet.frame.locals [cfU32V 5] hRelRetTB hSigShared rfl rfl rfl rfl
    .BottomOfStack f1TB f2TB cm1TB cm2TB hSLTB hAATB hF2TB
  have hLawArgBM := closure_typed_sig_call_correspondence_M (M := BM) sBadArg (cfPtrCaller sigArg (.uint .u64))
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    sBadArg.frame.locals sBadArg.frame.locals [.scalar ⟨5, 8⟩] hRelArgBM hSigShared rfl rfl rfl rfl
    .BottomOfStack f1BM f2BM cm1BM cm2BM hSLBM hAABM hF2BM
  have hLawArgTB := closure_typed_sig_call_correspondence_M (M := TBM) sBadArg (cfPtrCaller sigArg (.uint .u64))
    (.copy (locPlace 1)) [.copy (locPlace 2)] (locPlace 0) 1 .continue_ "ptr_call"
    sBadArg.frame.locals sBadArg.frame.locals [.scalar ⟨5, 8⟩] hRelArgTB hSigShared rfl rfl rfl rfl
    .BottomOfStack f1TB f2TB cm1TB cm2TB hSLTB hAATB hF2TB
  have hBadIn : ∀ retDecl envDecl paramDecls,
      cfFx_fn_shared_closure_0.localDecls = retDecl :: envDecl :: paramDecls →
      calleeParamTysMatch [] [.uint .u64] paramDecls = false := by
    intro r e ps h; cases h; rfl
  have hRetPairBM := hLawRetBM.2.1 (cfEntry cfSharedPath sigRet) [cfU32K] (.uint .u64) .safe u64MrTy
    [(.Int 5, u32MrTy)] rfl rfl rfl rfl rfl
  have hRetPairTB := hLawRetTB.2.1 (cfEntry cfSharedPath sigRet) [cfU32K] (.uint .u64) .safe u64MrTy
    [(.Int 5, u32MrTy)] rfl rfl rfl rfl rfl
  have hArgPairBM := hLawArgBM.2.2 (.uint .u32) [] (localName 1) [] (cfEntry cfSharedPath sigArg)
    (.uint .u64) [] cfU32K .safe (.Int 5) u64MrTy [] u32MrTy rfl rfl rfl rfl rfl rfl hBadIn rfl rfl rfl
  have hArgPairTB := hLawArgTB.2.2 (.uint .u32) [] (localName 1) [] (cfEntry cfSharedPath sigArg)
    (.uint .u64) [] cfU32K .safe (.Int 5) u64MrTy [] u32MrTy rfl rfl rfl rfl rfl rfl hBadIn rfl rfl rfl
  exact ⟨hRetPairBM.1, hRetPairBM.2, hRetPairTB.2, hArgPairBM.1, hArgPairBM.2, hArgPairTB.2⟩

/-! ## §6. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free Audit -/

section AxiomAudit
open Lean Elab Command

/-- Exhaustively verify that this module imports no `Anneal.*`, `Miri.*`, or
`LeanMiriSpec.*` module; that every declaration of this module depends only on
the standard axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero
`sorryAx` and zero `Lean.ofReduceBool`; that no non-internal theorem is
trivial; that the headline theorems exist; and that the executable runners,
reference machines, and the kernel-decided Trusted witnesses are
`Classical.choice`-free (the `MachTB.wfLive` witnesses use the classical
`wfLive` preservation lemmas of `MiniRustSpec.Correspondence`). -/
elab "#assert_closure_fn_ptr_mr_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || (`Miri).isPrefixOf modName ||
        (`LeanMiriSpec).isPrefixOf modName then
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
      if !u.isInternal then
        if isTrivialProp v.type then
          throwError "{c} is a trivial theorem"
        theorems := theorems + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool then throwError "{c} depends on Lean.ofReduceBool"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "MiniRustSpec.ClosureFnPtrMR: 0 declarations found"
  let headline : List Lean.Name := [
    ``checkClosureCalleeSig_callee_directed, ``closureFnPointer_reify_callee_directed,
    ``closureFnPointer_reify_fail_closed, ``closureFnPointer_normal_spelling_unsupported,
    ``closure_entry_frame_binds_env_then_args, ``closure_indirect_call_prepends_env,
    ``closure_indirect_tailCall_prepends_env, ``closure_indirect_call_fail_closed,
    ``closure_indirect_call_generic_unsupported, ``closure_direct_call_dispatches_unchanged,
    ``constEvalSelect_closure_runtime_target_dispatch, ``closure_reify_establishes_entryRel_M,
    ``closureFnPtrEntryRel_call_arity, ``closure_indirect_call_correspondence_M,
    ``classifyOwnClosureEnvTy_by_upvars, ``minirust_createFrameM_arity_law,
    ``minirust_createFrameM_abi_mismatch_law, ``closure_typed_sig_call_correspondence_M,
    ``minirust_ptr_rel_eq_same_addr_M, ``minirust_closure_call_return_tb_wfLive,
    ``closure_coercion_widening_identity_general_mach_and_tb,
    ``closure_coercion_widening_identity_mach_and_tb, ``cf_fn_closure_three_way_witness,
    ``cf_fnMut_closure_three_way_witness, ``cf_fnOnce_closure_three_way_witness,
    ``cf_zero_and_two_arg_closure_three_way_witness, ``cf_unsafe_closure_three_way_witness,
    ``cf_widen_and_identity_three_way_witness, ``cf_tailCall_closure_three_way_witness,
    ``cf_mixed_fnItem_and_closure_three_way_witness, ``cf_constEvalSelect_closure_three_way_witness,
    ``cf_finding_0007_parity_three_way_witness, ``cf_env_prepend_three_receiver_modes_witness,
    ``cf_coercion_fail_closed_witness, ``cf_indirect_call_fail_closed_three_way_witness,
    ``closure_indirect_call_law_instance_fn, ``closure_indirect_call_law_instance_fnMut,
    ``closure_indirect_call_law_instance_fnOnce, ``closureFnPtrEntryRel_instance_mach_and_tb,
    ``closure_indirect_call_correspondence_instance_mach_and_tb,
    ``closure_typed_sig_instances_mach_and_tb ]
  for c in headline do
    match env.find? c with
    | some (.thmInfo _) => pure ()
    | _ => throwError "headline theorem {c} is missing"
  let choiceFree : List Lean.Name := [
    ``cfRunStep, ``cfRun, ``cfInit, ``cfInitPtrs, ``cfShapeTag, ``cfShapeTag_inj, ``cfMrMach,
    ``cfMrIndirectMach, ``cfMrIdThenIndirectMach, ``cfMrWidenMach, ``cfMrMixedMach, ``cfMrFindingMach, ``cfCoerce, ``cfEntryObs,
    ``cfMrUb_of_decide, ``cf_env_prepend_three_receiver_modes_witness, ``cf_coercion_fail_closed_witness ]
  for c in choiceFree do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "{c} unexpectedly depends on Classical.choice"
  logInfo m!"MiniRustSpec.ClosureFnPtrMR: verified {checked} declarations, {theorems} non-internal theorems (sorry_free=true, ofReduceBool_free=true, import_isolated=true, headline={headline.length}, choice_free={choiceFree.length})"

#assert_closure_fn_ptr_mr_audit

end AxiomAudit

end MiniRustSpec.ClosureFnPtrMR
