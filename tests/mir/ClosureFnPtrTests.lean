/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Rustc.V2026_06_01.SymbolicEval
import Lean.Elab.Command

/-!
# Non-capturing closure to `fn`-pointer reification and indirect calls

Kernel-checked (`rfl`) tests for `ClosureFnPointer` coercions and calls through
the resulting function pointers in `Trusted.Rustc.V2026_06_01.MirSemantics` and
`Trusted.Rustc.V2026_08_01.MirSemantics`.

Every captured body in §1–§3 is the verbatim output of `anneal-rustc-capture`
run with the difftest capture flags
(`-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on --cfg anodized_embed_specs`):
§1 on a difftest reproducer whose closure coercion was reported as undefined
behavior while Miri returns `9147`, §2 on a crate exercising every closure
receiver mode, arity, `ClosureFnPointer(Safe|Unsafe)`, `UnsafeFnPointer`
widening, `FnPtrToPtr` identity, `TerminatorKind.tailCall`, diverging calls,
unwinding, mixed function-item and closure coercions, direct closure calls,
capturing closures, and a generic closure. §3 re-targets the §2 text at the
`V2026_08_01` AST (only the namespace of the opened `Trusted.Rustc.*` modules
and of the module itself changes).

§4 confirms the reproducer end to end with the difftest probe. §5 (`V2026_06_01`)
and §6 (`V2026_08_01`) run the same matrix in lockstep: positive executions,
fail-closed negative witnesses (capturing closures, forged `(N + 1)`-argument
calls, transmuted signatures, non-Rust ABIs, safety mismatches, a forged body
reading its environment), `.unsupported` (never `.ub`) for generic closures,
direct calls passing the environment explicitly, all four `UnwindAction`s, and
inline `const_eval_select` with closure runtime targets.
-/

/-! ## 1. Verbatim `rustc-capture` output: difftest reproducer (`V2026_06_01`) -/

namespace Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `miri_diff_corpus::pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=1, align=1
-- TypeLayout[5]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))) }

-- bb0: StorageLive(_1); _1 = PairU32 { a: const 7_u32, b: const 35_u32 }; StorageLive(_2); StorageLive(_3); _3 = &_1; _2 = &(*_3); StorageDead(_3); StorageLive(_4); _4 = &raw const ((*_2).1: u32); StorageLive(_5); StorageLive(_6); _6 = &(*_2); _5 = &(*_6); StorageDead(_6); StorageLive(_7); _7 = copy (*_4); StorageLive(_8); _8 = copy (*_4); StorageLive(_9); StorageLive(_10); StorageLive(_11); _11 = copy _7; StorageLive(_12); _12 = copy ((*_5).0: u32); _10 = BitXor(move _11, move _12); StorageDead(_12); StorageDead(_11); StorageLive(_13); StorageLive(_14); _14 = copy _8; _15 = Lt(const 8_u32, const 32_u32); assert(move _15, "attempt to shift left by `{}`, which would overflow", const 8_u32) -> [success: bb1, unwind continue]
-- bb1: _13 = Shl(move _14, const 8_u32); StorageDead(_14); _9 = BitXor(move _10, move _13); StorageDead(_13); StorageDead(_10); StorageLive(_16); StorageLive(_17); StorageLive(_18); _18 = copy _7; _17 = BitAnd(move _18, const 65535_u32); StorageDead(_18); _16 = __anneal_vt_driver_61873(move _17, const 24_u32) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_17); StorageLive(_19); _19 = copy _9; StorageLive(_20); _20 = copy _16; _0 = BitXor(move _19, move _20); StorageDead(_20); StorageDead(_19); StorageDead(_16); StorageDead(_9); StorageDead(_8); StorageDead(_7); StorageDead(_5); StorageDead(_4); StorageDead(_2); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 1 }, debugName := (Option.some "pair") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := (Option.some "tmp") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 3 }, debugName := (Option.some "raw") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := (Option.some "shared") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "miri_diff_corpus::PairU32" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "first") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "again") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_vt_61873") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_vt_61873") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 15), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:288:9: 288:13" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::PairU32" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 35, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:288:25: 288:54" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:289:9: 289:12" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:289:25: 289:30" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 1, projection := List.nil })), span := "src/lib.rs:289:25: 289:30" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 3, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:289:25: 289:30" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:289:30: 289:31" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:290:9: 290:12" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 2, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) })), span := "src/lib.rs:290:27: 290:46" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:291:9: 291:15" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:291:28: 291:33" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:291:28: 291:33" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 6, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:291:28: 291:33" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:291:33: 291:34" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:292:9: 292:14" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:292:31: 292:35" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:293:9: 293:14" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:293:31: 293:35" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:294:9: 294:31" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:294:39: 294:55" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:294:39: 294:44" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:294:39: 294:44" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:294:47: 294:55" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:294:47: 294:55" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 11, projection := List.nil }) (Operand.move { local_ := 12, projection := List.nil }))), span := "src/lib.rs:294:39: 294:55" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:294:54: 294:55" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:294:54: 294:55" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:294:58: 294:73" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:294:59: 294:64" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 8, projection := List.nil }))), span := "src/lib.rs:294:59: 294:64" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:294:58: 294:73" } List.nil)))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 15, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:294:58: 294:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 14, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }))), span := "src/lib.rs:294:58: 294:73" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:294:72: 294:73" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 10, projection := List.nil }) (Operand.move { local_ := 13, projection := List.nil }))), span := "src/lib.rs:294:39: 294:73" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:294:72: 294:73" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:294:72: 294:73" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:295:9: 295:24" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:296:9: 296:35" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:296:9: 296:23" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:296:10: 296:15" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 18, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 65535, sizeBytes := 4 })) }))), span := "src/lib.rs:296:9: 296:35" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:296:34: 296:35" } List.nil))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "miri_diff_corpus::__anneal_vt_driver_61873" List.nil), layoutIdx := 5 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 17, projection := List.nil }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }) List.nil)) { local_ := 16, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:295:32: 298:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:298:5: 298:6" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:299:5: 299:27" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:299:5: 299:27" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:299:30: 299:54" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:299:31: 299:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 19, projection := List.nil }) (Operand.move { local_ := 20, projection := List.nil }))), span := "src/lib.rs:299:5: 299:54" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:299:53: 299:54" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:299:53: 299:54" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:300:1: 300:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:300:1: 300:2" } List.nil)))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:300:2: 300:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27

namespace Mir.MiriDiffCorpus.__anneal_vt_driver_61873

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `miri_diff_corpus::__anneal_vt_driver_61873`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=1, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:273:36: 273:49}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); StorageLive(_6); _6 = copy _3; _5 = move _6 as unsafe fn(u32) -> u32 (PointerCoercion(UnsafeFnPointer, Implicit)); StorageDead(_6); StorageLive(_7); StorageLive(_8); _8 = {closure@src/lib.rs:275:51: 275:64}; _7 = move _8 as unsafe fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Unsafe), Implicit)); StorageDead(_8); StorageLive(_9); StorageLive(_10); _10 = copy _3; _9 = move _10 as *const () (FnPtrToPtr); StorageDead(_10); StorageLive(_11); StorageLive(_12); _12 = copy _5; _11 = move _12 as *const () (FnPtrToPtr); StorageDead(_12); StorageLive(_13); StorageLive(_14); _14 = copy _3; StorageLive(_15); _15 = copy _1; _13 = move _14(move _15) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_15); StorageDead(_14); StorageLive(_16); StorageLive(_17); _17 = copy _5; StorageLive(_18); StorageLive(_19); _19 = copy _13; StorageLive(_20); _20 = copy _2; _18 = BitXor(move _19, move _20); StorageDead(_20); StorageDead(_19); _16 = move _17(move _18) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_18); StorageDead(_17); StorageLive(_21); StorageLive(_22); _22 = copy _7; StorageLive(_23); StorageLive(_24); _24 = copy _16; _23 = BitXor(move _24, const 24_u32); StorageDead(_24); _21 = move _22(move _23) -> [return: bb3, unwind continue]
-- bb3: StorageDead(_23); StorageDead(_22); StorageLive(_25); StorageLive(_26); StorageLive(_27); _27 = copy _9; StorageLive(_28); _28 = copy _11; _26 = Eq(move _27, move _28); switchInt(move _26) -> [0: bb5, otherwise: bb4]
-- bb4: StorageDead(_28); StorageDead(_27); _25 = const 1_u32; goto -> bb6
-- bb5: StorageDead(_28); StorageDead(_27); _25 = const 0_u32; goto -> bb6
-- bb6: StorageDead(_26); StorageLive(_29); StorageLive(_30); StorageLive(_31); _31 = copy _13; StorageLive(_32); StorageLive(_33); _33 = copy _16; _34 = Lt(const 1_u32, const 32_u32); assert(move _34, "attempt to shift left by `{}`, which would overflow", const 1_u32) -> [success: bb7, unwind continue]
-- bb7: _32 = Shl(move _33, const 1_u32); StorageDead(_33); _30 = BitXor(move _31, move _32); StorageDead(_32); StorageDead(_31); StorageLive(_35); StorageLive(_36); _36 = copy _21; _37 = Lt(const 2_u32, const 32_u32); assert(move _37, "attempt to shift left by `{}`, which would overflow", const 2_u32) -> [success: bb8, unwind continue]
-- bb8: _35 = Shl(move _36, const 2_u32); StorageDead(_36); _29 = BitXor(move _30, move _35); StorageDead(_35); StorageDead(_30); StorageLive(_38); _38 = copy _25; _0 = BitXor(move _29, move _38); StorageDead(_38); StorageDead(_29); StorageDead(_25); StorageDead(_21); StorageDead(_16); StorageDead(_13); StorageDead(_11); StorageDead(_9); StorageDead(_7); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_61873",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_seed") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_bias") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "__vt_cfp") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "__vt_cufp") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "__vt_cufp_direct") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := (Option.some "__vt_raw_c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := (Option.some "__vt_raw_d") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_first") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_second") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_third") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_same") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 34), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 37), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:273:9: 273:17" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:273:36: 273:77" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}") List.nil)), span := "src/lib.rs:273:36: 273:77" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:273:36: 273:77" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:273:48: 273:49" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:274:9: 274:18" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:274:44: 274:52" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:274:44: 274:52" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "UnsafeFnPointer") (Operand.move { local_ := 6, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:274:44: 274:52" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:274:51: 274:52" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:275:9: 275:25" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:275:51: 275:79" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}") List.nil)), span := "src/lib.rs:275:51: 275:79" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Unsafe)") (Operand.move { local_ := 8, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:275:51: 275:79" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:275:63: 275:64" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:276:9: 276:19" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:276:33: 276:41" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:276:33: 276:41" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 10, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 })), span := "src/lib.rs:276:33: 276:54" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:276:53: 276:54" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:277:9: 277:19" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:277:33: 277:42" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:277:33: 277:42" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 12, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 })), span := "src/lib.rs:277:33: 277:55" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:277:54: 277:55" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:278:9: 278:19" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:278:27: 278:35" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:278:27: 278:35" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:278:36: 278:45" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:278:36: 278:45" } List.nil)))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 14, projection := List.nil }) (List.cons (Operand.move { local_ := 15, projection := List.nil }) List.nil) { local_ := 13, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:278:27: 278:46" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:278:45: 278:46" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:278:45: 278:46" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:279:9: 279:20" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:279:37: 279:46" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := List.nil }))), span := "src/lib.rs:279:37: 279:46" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:279:47: 279:69" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:279:47: 279:57" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 13, projection := List.nil }))), span := "src/lib.rs:279:47: 279:57" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:279:60: 279:69" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:279:60: 279:69" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 19, projection := List.nil }) (Operand.move { local_ := 20, projection := List.nil }))), span := "src/lib.rs:279:47: 279:69" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:279:68: 279:69" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:279:68: 279:69" } List.nil))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 17, projection := List.nil }) (List.cons (Operand.move { local_ := 18, projection := List.nil }) List.nil) { local_ := 16, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:279:37: 279:70" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:279:69: 279:70" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:279:69: 279:70" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:280:9: 280:19" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:280:36: 280:52" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:280:36: 280:52" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:280:53: 280:72" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:280:53: 280:64" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:280:53: 280:64" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 24, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 24, sizeBytes := 4 })) }))), span := "src/lib.rs:280:53: 280:72" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:280:71: 280:72" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 22, projection := List.nil }) (List.cons (Operand.move { local_ := 23, projection := List.nil }) List.nil) { local_ := 21, projection := List.nil } (Option.some 3) UnwindAction.continue_), span := "src/lib.rs:280:36: 280:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:280:72: 280:73" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:280:72: 280:73" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:281:9: 281:18" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:281:29: 281:53" } (List.cons { kind := (StatementKind.storageLive 27), span := "src/lib.rs:281:29: 281:39" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 9, projection := List.nil }))), span := "src/lib.rs:281:29: 281:39" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:281:43: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 11, projection := List.nil }))), span := "src/lib.rs:281:43: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 27, projection := List.nil }) (Operand.move { local_ := 28, projection := List.nil }))), span := "src/lib.rs:281:29: 281:53" } List.nil))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 26, projection := List.nil }) { branches := (List.cons (0, 5) List.nil), otherwise := 4 }), span := "src/lib.rs:281:29: 281:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:281:56: 281:60" } List.nil))), terminator := { kind := (TerminatorKind.goto 6), span := "src/lib.rs:281:26: 281:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.storageDead 27), span := "src/lib.rs:281:52: 281:53" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:281:70: 281:74" } List.nil))), terminator := { kind := (TerminatorKind.goto 6), span := "src/lib.rs:281:26: 281:76" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:281:75: 281:76" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:282:5: 282:62" } (List.cons { kind := (StatementKind.storageLive 30), span := "src/lib.rs:282:5: 282:39" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:282:5: 282:15" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 13, projection := List.nil }))), span := "src/lib.rs:282:5: 282:15" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:282:18: 282:39" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:282:19: 282:30" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:282:19: 282:30" } (List.cons { kind := (StatementKind.assign { local_ := 34, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:282:18: 282:39" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 34, projection := List.nil }) true 7 UnwindAction.continue_), span := "src/lib.rs:282:18: 282:39" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 33, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:282:18: 282:39" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:282:38: 282:39" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 31, projection := List.nil }) (Operand.move { local_ := 32, projection := List.nil }))), span := "src/lib.rs:282:5: 282:39" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:282:38: 282:39" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:282:38: 282:39" } (List.cons { kind := (StatementKind.storageLive 35), span := "src/lib.rs:282:42: 282:62" } (List.cons { kind := (StatementKind.storageLive 36), span := "src/lib.rs:282:43: 282:53" } (List.cons { kind := (StatementKind.assign { local_ := 36, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 21, projection := List.nil }))), span := "src/lib.rs:282:43: 282:53" } (List.cons { kind := (StatementKind.assign { local_ := 37, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:282:42: 282:62" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 37, projection := List.nil }) true 8 UnwindAction.continue_), span := "src/lib.rs:282:42: 282:62" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 35, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 36, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:282:42: 282:62" } (List.cons { kind := (StatementKind.storageDead 36), span := "src/lib.rs:282:61: 282:62" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 30, projection := List.nil }) (Operand.move { local_ := 35, projection := List.nil }))), span := "src/lib.rs:282:5: 282:62" } (List.cons { kind := (StatementKind.storageDead 35), span := "src/lib.rs:282:61: 282:62" } (List.cons { kind := (StatementKind.storageDead 30), span := "src/lib.rs:282:61: 282:62" } (List.cons { kind := (StatementKind.storageLive 38), span := "src/lib.rs:282:65: 282:74" } (List.cons { kind := (StatementKind.assign { local_ := 38, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 25, projection := List.nil }))), span := "src/lib.rs:282:65: 282:74" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 29, projection := List.nil }) (Operand.move { local_ := 38, projection := List.nil }))), span := "src/lib.rs:282:5: 282:74" } (List.cons { kind := (StatementKind.storageDead 38), span := "src/lib.rs:282:73: 282:74" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:282:73: 282:74" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:283:1: 283:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:283:1: 283:2" } List.nil))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:283:2: 283:2" }, isCleanup := false } List.nil))))))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.MiriDiffCorpus.__anneal_vt_driver_61873

namespace Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_z") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:273:63: 273:69" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:273:63: 273:69" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:273:50: 273:77" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:273:76: 273:77" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:273:77: 273:77" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_0

namespace Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_1

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__vt_z") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:275:65: 275:71" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:275:65: 275:71" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:275:65: 275:79" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:275:78: 275:79" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:275:79: 275:79" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_1


/-! ## 2. Verbatim `rustc-capture` output: closure matrix crate (`V2026_06_01`) -/

namespace Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::<Guard as core::ops::Drop>::drop`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=4, align=4
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: _0 = const (); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::<Guard as core::ops::Drop>::drop",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "core::ops::Drop::drop", args := (List.cons (RigidTy.adt "closure_matrix::Guard" List.nil) List.nil) }, implPath := "closure_matrix::<Guard as core::ops::Drop>::drop" } List.nil),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.adt "closure_matrix::Guard" List.nil)), layoutIdx := 3 }, debugName := (Option.some "self") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:80:24: 80:26" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:80:26: 80:26" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop

namespace Mir.ClosureMatrix.call_generic

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::call_generic`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: StorageLive(_2); _2 = copy _1; _0 = generic_closure::<u32>(move _2) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::call_generic",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:109:28: 109:29" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:109:28: 109:29" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::generic_closure" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 2, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:109:5: 109:30" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:109:29: 109:30" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:110:2: 110:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.call_generic

namespace Mir.ClosureMatrix.capturing_direct

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::capturing_direct`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=4, align=4
-- TypeLayout[3]: size=0, align=1
-- TypeLayout[4]: size=8, align=8
-- TypeLayout[5]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) } List.nil)))))) }

-- bb0: StorageLive(_3); _3 = (); StorageLive(_4); _4 = {closure@src/lib.rs:114:17: 114:30} { y: copy _2 }; StorageLive(_5); _5 = {closure@src/lib.rs:115:15: 115:28} { unit: copy _3 }; StorageLive(_6); StorageLive(_7); _7 = &_4; StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = (move _9,); _6 = <{closure@src/lib.rs:114:17: 114:30} as core::ops::Fn<(u32,)>>::call(move _7, move _8) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_9); StorageDead(_8); StorageDead(_7); StorageLive(_10); StorageLive(_11); _11 = &_5; StorageLive(_12); StorageLive(_13); _13 = copy _1; _12 = (move _13,); _10 = <{closure@src/lib.rs:115:15: 115:28} as core::ops::Fn<(u32,)>>::call(move _11, move _12) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_13); StorageDead(_12); StorageDead(_11); _0 = BitXor(move _6, move _10); StorageDead(_10); StorageDead(_6); StorageDead(_5); StorageDead(_4); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := (Option.some "unit") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := (Option.some "add_y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil)), layoutIdx := 3 }, debugName := (Option.some "zst") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:113:9: 113:13" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple List.nil)), span := "src/lib.rs:113:16: 113:18" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:114:9: 114:14" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::capturing_direct::{closure#0}") (List.cons (Operand.copy { local_ := 2, projection := List.nil }) List.nil))), span := "src/lib.rs:114:17: 114:49" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:115:9: 115:12" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::capturing_direct::{closure#1}") (List.cons (Operand.copy { local_ := 3, projection := List.nil }) List.nil))), span := "src/lib.rs:115:15: 118:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:119:5: 119:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:119:5: 119:10" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 4, projection := List.nil })), span := "src/lib.rs:119:5: 119:10" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:119:5: 119:13" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:119:11: 119:12" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:119:11: 119:12" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 9, projection := List.nil }) List.nil))), span := "src/lib.rs:119:5: 119:13" } List.nil))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil)) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil)) { local_ := 6, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:119:5: 119:13" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:119:16: 119:22" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:119:16: 119:19" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 5, projection := List.nil })), span := "src/lib.rs:119:16: 119:19" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:119:16: 119:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:119:20: 119:21" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:119:20: 119:21" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 13, projection := List.nil }) List.nil))), span := "src/lib.rs:119:16: 119:22" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil)) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 11, projection := List.nil }) (List.cons (Operand.move { local_ := 12, projection := List.nil }) List.nil)) { local_ := 10, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:119:16: 119:22" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 6, projection := List.nil }) (Operand.move { local_ := 10, projection := List.nil }))), span := "src/lib.rs:119:5: 119:22" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:120:1: 120:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:120:1: 120:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:120:1: 120:2" } List.nil))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:120:2: 120:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.capturing_direct

namespace Mir.ClosureMatrix.capturing_direct_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::capturing_direct::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; StorageLive(_4); _4 = copy ((*_1).0: u32); _0 = Add(move _3, move _4); StorageDead(_4); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:114:44: 114:45" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:114:44: 114:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:114:47: 114:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:114:47: 114:48" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.move { local_ := 4, projection := List.nil }))), span := "src/lib.rs:114:31: 114:49" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:114:48: 114:49" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:114:48: 114:49" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:114:49: 114:49" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.capturing_direct_closure_0

namespace Mir.ClosureMatrix.capturing_direct_closure_1

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::capturing_direct::{closure#1}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil)))) }

-- bb0: StorageLive(_3); _3 = copy ((*_1).0: ()); _0 = copy _2; StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct::{closure#1}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil))), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := (Option.some "_keep") } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:116:13: 116:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }) List.nil)) }))), span := "src/lib.rs:116:21: 116:25" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:117:9: 117:10" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:118:5: 118:6" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:118:6: 118:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.capturing_direct_closure_1

namespace Mir.ClosureMatrix.ces_through_closure_fn_ptr

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::ces_through_closure_fn_ptr`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:99:30: 99:38}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = (move _5,); StorageDead(_5); StorageLive(_6); _6 = copy _2; _0 = move _6(move (_4.0: u32)) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::ces_through_closure_fn_ptr",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "rt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:99:9: 99:11" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}") List.nil)), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:99:37: 99:38" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:100:23: 100:27" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:100:24: 100:25" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:100:24: 100:25" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil))), span := "src/lib.rs:100:23: 100:27" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:100:26: 100:27" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:100:37: 100:39" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:100:37: 100:39" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:100:5: 100:40" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:100:39: 100:40" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:100:39: 100:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:101:1: 101:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:101:2: 101:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.ces_through_closure_fn_ptr

namespace Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::ces_through_closure_fn_ptr::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::ces_through_closure_fn_ptr::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:99:52: 99:53" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:99:52: 99:53" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:99:39: 99:61" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:99:60: 99:61" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:99:61: 99:61" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0

namespace Mir.ClosureMatrix.ct_add

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::ct_add`. -/

-- TypeLayout[0]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = copy _1; return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::ct_add",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:95:5: 95:6" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:96:2: 96:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.ct_add

namespace Mir.ClosureMatrix.direct_closure_call

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::direct_closure_call`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil)))) }

-- bb0: StorageLive(_2); _2 = {closure@src/lib.rs:90:13: 90:21}; StorageLive(_3); _3 = &_2; StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = (move _5,); _0 = <{closure@src/lib.rs:90:13: 90:21} as core::ops::Fn<(u32,)>>::call(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::direct_closure_call",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:90:9: 90:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::direct_closure_call::{closure#0}") List.nil)), span := "src/lib.rs:90:13: 90:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:91:5: 91:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:91:5: 91:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:91:5: 91:9" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:91:7: 91:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:91:7: 91:8" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil))), span := "src/lib.rs:91:5: 91:9" } List.nil)))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:91:5: 91:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:92:1: 92:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:92:2: 92:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.direct_closure_call

namespace Mir.ClosureMatrix.direct_closure_call_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::direct_closure_call::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 9_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::direct_closure_call::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:90:35: 90:36" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:90:35: 90:36" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:90:22: 90:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:90:42: 90:43" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:90:43: 90:43" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.direct_closure_call_closure_0

namespace Mir.ClosureMatrix.diverging_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::diverging_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } List.nil))))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:73:27: 73:35}; _2 = move _3 as fn(u32) -> ! (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = Eq(move _5, const 0_u32); switchInt(move _4) -> [0: bb2, otherwise: bb1]
-- bb1: StorageDead(_5); StorageLive(_6); StorageLive(_7); _7 = copy _2; StorageLive(_8); _8 = copy _1; _6 = move _7(move _8) -> unwind continue
-- bb2: StorageDead(_5); _0 = copy _1; StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::diverging_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) RigidTy.never Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::diverging_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) RigidTy.never Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:73:9: 73:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:73:27: 73:62" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::diverging_closure::{closure#0}") List.nil)), span := "src/lib.rs:73:27: 73:62" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) RigidTy.never Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:73:27: 73:62" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:73:34: 73:35" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:74:8: 74:17" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:74:8: 74:9" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:74:8: 74:9" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:74:8: 74:17" } List.nil))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 4, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:74:8: 74:17" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:74:16: 74:17" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:74:20: 74:24" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:74:20: 74:21" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:74:20: 74:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:74:22: 74:23" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:74:22: 74:23" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil) { local_ := 6, projection := List.nil } Option.none UnwindAction.continue_), span := "src/lib.rs:74:20: 74:24" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:74:16: 74:17" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:74:34: 74:35" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:74:36: 74:37" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:75:1: 75:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:75:2: 75:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.diverging_closure

namespace Mir.ClosureMatrix.diverging_closure_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::diverging_closure::{closure#0}`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=4, align=4
-- TypeLayout[4]: size=8, align=8
-- TypeLayout[5]: size=8, align=8
-- TypeLayout[6]: size=16, align=8
-- TypeLayout[7]: size=16, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 4 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 5 (List.cons 5 List.nil)) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = core::fmt::Arguments::<'_>::from_str(const "closure diverged") -> [return: bb1, unwind continue]
-- bb1: _3 = core::panicking::panic_fmt(move _4) -> unwind continue
def body : CapturedMir :=
  {
    defPath := "closure_matrix::diverging_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::diverging_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 3 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.never, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::fmt::Arguments" List.nil), layoutIdx := 6 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" } (List.cons { kind := (StatementKind.storageLive 4), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::fmt::Arguments::<'a>::from_str" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 7 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 16) }) List.nil) { local_ := 4, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::panicking::panic_fmt" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil) { local_ := 3, projection := List.nil } Option.none UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := (List.cons { allocId := 1, bytes := (List.cons (Option.some (UInt8.ofNat 99)) (List.cons (Option.some (UInt8.ofNat 108)) (List.cons (Option.some (UInt8.ofNat 111)) (List.cons (Option.some (UInt8.ofNat 115)) (List.cons (Option.some (UInt8.ofNat 117)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 32)) (List.cons (Option.some (UInt8.ofNat 100)) (List.cons (Option.some (UInt8.ofNat 105)) (List.cons (Option.some (UInt8.ofNat 118)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 103)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 100)) List.nil)))))))))))))))), relocations := List.nil, align := { bytes := 1 }, mutability := Mutability.not } List.nil)
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.diverging_closure_closure_0

namespace Mir.ClosureMatrix.fn_mut_kind

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_mut_kind`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:28:20: 28:28}; _2 = id_mut::<{closure@src/lib.rs:28:20: 28:28}>(move _3) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_7); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_mut_kind",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:28:9: 28:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:20: 28:50" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_mut_kind::{closure#0}") List.nil)), span := "src/lib.rs:28:20: 28:50" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::id_mut" (List.cons (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil) { local_ := 2, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:28:13: 28:51" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:50: 28:51" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:29:9: 29:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:30:5: 30:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:30:5: 30:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:30:7: 30:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:30:7: 30:8" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:30:5: 30:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:30:8: 30:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:30:8: 30:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:31:1: 31:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:31:1: 31:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:31:2: 31:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.fn_mut_kind

namespace Mir.ClosureMatrix.fn_mut_kind_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_mut_kind::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 2_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_mut_kind::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:42: 28:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:28:42: 28:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:28:29: 28:50" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:49: 28:50" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:28:50: 28:50" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.fn_mut_kind_closure_0

namespace Mir.ClosureMatrix.fn_once_kind

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_once_kind`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:34:21: 34:29}; _2 = id_once::<{closure@src/lib.rs:34:21: 34:29}>(move _3) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_7); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_once_kind",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:34:9: 34:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:34:21: 34:51" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_once_kind::{closure#0}") List.nil)), span := "src/lib.rs:34:21: 34:51" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::id_once" (List.cons (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil) { local_ := 2, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:34:13: 34:52" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:34:51: 34:52" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:35:9: 35:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:36:5: 36:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:36:5: 36:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:36:7: 36:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:36:7: 36:8" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:36:5: 36:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:36:8: 36:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:36:8: 36:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:37:1: 37:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:37:1: 37:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:37:2: 37:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.fn_once_kind

namespace Mir.ClosureMatrix.fn_once_kind_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_once_kind::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 3_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_once_kind::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:34:43: 34:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:34:43: 34:44" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:34:30: 34:51" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:34:50: 34:51" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:34:51: 34:51" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.fn_once_kind_closure_0

namespace Mir.ClosureMatrix.fn_shared

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_shared`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:23:29: 23:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_shared",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_shared::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:23:9: 23:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_shared::{closure#0}") List.nil)), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:36: 23:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:24:5: 24:6" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:24:5: 24:6" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:24:7: 24:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:24:7: 24:8" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:24:5: 24:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:24:8: 24:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:24:8: 24:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:25:1: 25:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:25:2: 25:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.fn_shared

namespace Mir.ClosureMatrix.fn_shared_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_shared::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_shared::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::fn_shared::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:23:51: 23:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:23:51: 23:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:23:38: 23:60" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:59: 23:60" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:23:60: 23:60" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.fn_shared_closure_0

namespace Mir.ClosureMatrix.generic_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::generic_closure`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:104:25: 104:31}; _2 = move _3 as fn(T) -> T (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.generic_closure

namespace Mir.ClosureMatrix.generic_closure_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::generic_closure::{closure#0}`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: _0 = copy _2; return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.generic_closure_closure_0

namespace Mir.ClosureMatrix.helper_triple

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::helper_triple`. -/

-- TypeLayout[0]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: StorageLive(_2); _2 = copy _1; _0 = Mul(move _2, const 3_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::helper_triple",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:19:18: 19:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:19:18: 19:19" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.mul (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:19:5: 19:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:19:25: 19:26" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:20:2: 20:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.helper_triple

namespace Mir.ClosureMatrix.id_mut

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::id_mut`. -/

-- TypeLayout[0]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = move _1; return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.id_mut

namespace Mir.ClosureMatrix.id_once

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::id_once`. -/

-- TypeLayout[0]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = move _1; return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.id_once

namespace Mir.ClosureMatrix.mixed_fn_item_and_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::mixed_fn_item_and_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); _2 = helper_triple as fn(u32) -> u32 (PointerCoercion(ReifyFnPointer(Safe), Implicit)); StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:63:29: 63:37}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; StorageLive(_7); _7 = copy _1; _5 = move _6(move _7) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_7); StorageDead(_6); StorageLive(_8); StorageLive(_9); _9 = copy _3; StorageLive(_10); _10 = copy _1; _8 = move _9(move _10) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_10); StorageDead(_9); _0 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::mixed_fn_item_and_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:62:9: 62:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ReifyFnPointer(Safe)") (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::helper_triple" List.nil), layoutIdx := 2 }, val := ConstValue.zeroSized }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:62:29: 62:42" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:63:9: 63:10" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}") List.nil)), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:63:36: 63:37" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:64:5: 64:9" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:64:5: 64:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:64:5: 64:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:64:7: 64:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:64:7: 64:8" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 5, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:64:5: 64:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:64:8: 64:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:64:8: 64:9" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:64:12: 64:16" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:64:12: 64:13" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:64:12: 64:13" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:64:14: 64:15" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:64:14: 64:15" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 9, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil) { local_ := 8, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:64:12: 64:16" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:64:5: 64:16" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:65:1: 65:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:65:1: 65:2" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:65:2: 65:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.mixed_fn_item_and_closure

namespace Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::mixed_fn_item_and_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Mul(move _3, const 5_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::mixed_fn_item_and_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:63:51: 63:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:63:51: 63:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.mul (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:63:38: 63:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:63:58: 63:59" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:63:59: 63:59" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0

namespace Mir.ClosureMatrix.tail_through_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::tail_through_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:68:29: 68:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; StorageLive(_6); _6 = copy _1; tailcall move _5(move _6)
def body : CapturedMir :=
  {
    defPath := "closure_matrix::tail_through_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::tail_through_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:68:9: 68:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::tail_through_closure::{closure#0}") List.nil)), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:68:36: 68:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:69:5: 69:16" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:69:12: 69:13" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:69:12: 69:13" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:69:14: 69:15" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:69:14: 69:15" } List.nil)))))))))), terminator := { kind := (TerminatorKind.tailCall (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil)), span := "src/lib.rs:69:5: 69:16" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.tail_through_closure

namespace Mir.ClosureMatrix.tail_through_closure_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::tail_through_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 5_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::tail_through_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::tail_through_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:68:38: 68:39" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:68:38: 68:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:68:38: 68:46" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:68:45: 68:46" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:68:46: 68:46" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.tail_through_closure_closure_0

namespace Mir.ClosureMatrix.two_arg

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::two_arg`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:45:34: 45:50}; _3 = move _4 as fn(u32, u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); _6 = copy _1; StorageLive(_7); _7 = copy _2; _0 = move _5(move _6, move _7) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_7); StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::two_arg",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::two_arg::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:45:9: 45:10" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::two_arg::{closure#0}") List.nil)), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:45:49: 45:50" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:46:5: 46:6" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:46:5: 46:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:46:7: 46:8" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:46:7: 46:8" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:46:10: 46:11" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:46:10: 46:11" } List.nil))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:46:5: 46:12" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:47:1: 47:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:47:2: 47:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.two_arg

namespace Mir.ClosureMatrix.two_arg_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::two_arg::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _3; _0 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::two_arg::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 3,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::two_arg::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:45:51: 45:52" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:45:51: 45:52" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:45:51: 45:56" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:45:55: 45:56" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:45:56: 45:56" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil))), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.two_arg_closure_0

namespace Mir.ClosureMatrix.unsafe_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unsafe_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:50:36: 50:44}; _2 = move _3 as unsafe fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Unsafe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unsafe_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::unsafe_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:50:9: 50:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::unsafe_closure::{closure#0}") List.nil)), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Unsafe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:50:43: 50:44" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:51:14: 51:15" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:51:14: 51:15" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:51:16: 51:17" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:51:16: 51:17" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:51:14: 51:18" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:51:17: 51:18" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:51:17: 51:18" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:52:1: 52:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:52:2: 52:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.unsafe_closure

namespace Mir.ClosureMatrix.unsafe_closure_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unsafe_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unsafe_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::unsafe_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:50:45: 50:46" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:50:45: 50:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:50:45: 50:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:50:53: 50:54" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:50:54: 50:54" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.unsafe_closure_closure_0

namespace Mir.ClosureMatrix.unwind_through_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unwind_through_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy _1; _2 = Guard(move _3); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = {closure@src/lib.rs:85:29: 85:37}; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb1, unwind: bb3]
-- bb1: StorageDead(_7); StorageDead(_6); StorageDead(_4); drop(_2) -> [return: bb2, unwind: bb4]
-- bb2: StorageDead(_2); return
-- bb3: drop(_2) -> [return: bb4, unwind terminate(cleanup)]
-- bb4: resume
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unwind_through_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_matrix::Guard" List.nil), layoutIdx := 1 }, debugName := (Option.some "_g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::unwind_through_closure::{closure#0}" List.nil), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:84:9: 84:11" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:84:20: 84:21" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:84:20: 84:21" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_matrix::Guard" 0 Option.none) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil))), span := "src/lib.rs:84:14: 84:22" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:84:21: 84:22" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:85:9: 85:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::unwind_through_closure::{closure#0}") List.nil)), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:85:36: 85:37" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:86:5: 86:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:86:5: 86:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:86:7: 86:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:86:7: 86:8" } List.nil)))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) (UnwindAction.cleanup 3)), span := "src/lib.rs:86:5: 86:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:86:8: 86:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:86:8: 86:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:87:1: 87:2" } List.nil))), terminator := { kind := (TerminatorKind.drop { local_ := 2, projection := List.nil } 2 (UnwindAction.cleanup 4)), span := "src/lib.rs:87:1: 87:2" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:87:1: 87:2" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:87:2: 87:2" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.drop { local_ := 2, projection := List.nil } 4 UnwindAction.terminate), span := "src/lib.rs:87:1: 87:2" }, isCleanup := true } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unwindResume, span := "src/lib.rs:83:1: 87:2" }, isCleanup := true } List.nil))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.unwind_through_closure

namespace Mir.ClosureMatrix.unwind_through_closure_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unwind_through_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=0, align=1
-- TypeLayout[5]: size=8, align=8
-- TypeLayout[6]: size=8, align=8
-- TypeLayout[7]: size=16, align=8
-- TypeLayout[8]: size=16, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 5 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 6 (List.cons 6 List.nil)) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; _3 = Eq(move _4, const 0_u32); switchInt(move _3) -> [0: bb3, otherwise: bb1]
-- bb1: StorageDead(_4); StorageLive(_6); StorageLive(_7); _7 = core::fmt::Arguments::<'_>::from_str(const "zero") -> [return: bb2, unwind continue]
-- bb2: _6 = core::panicking::panic_fmt(move _7) -> unwind continue
-- bb3: StorageDead(_4); _0 = copy _2; StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unwind_through_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::unwind_through_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::fmt::Arguments" List.nil), layoutIdx := 7 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:85:41: 85:50" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:85:41: 85:42" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:85:41: 85:42" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 4, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:85:41: 85:50" } List.nil)))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 1 }), span := "src/lib.rs:85:41: 85:50" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:85:49: 85:50" } (List.cons { kind := (StatementKind.storageLive 6), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" } (List.cons { kind := (StatementKind.storageLive 7), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::fmt::Arguments::<'a>::from_str" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 8 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 4) }) List.nil) { local_ := 7, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::panicking::panic_fmt" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 6, projection := List.nil } Option.none UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:85:49: 85:50" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:85:77: 85:78" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:85:79: 85:80" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:85:80: 85:80" }, isCleanup := false } List.nil)))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := (List.cons { allocId := 1, bytes := (List.cons (Option.some (UInt8.ofNat 122)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 111)) List.nil)))), relocations := List.nil, align := { bytes := 1 }, mutability := Mutability.not } List.nil)
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.unwind_through_closure_closure_0

namespace Mir.ClosureMatrix.widen_and_identity

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::widen_and_identity`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil))))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:55:29: 55:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as unsafe fn(u32) -> u32 (PointerCoercion(UnsafeFnPointer, Implicit)); StorageDead(_5); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _2; _8 = move _9 as *const () (FnPtrToPtr); StorageDead(_9); StorageLive(_10); StorageLive(_11); _11 = copy _4; _10 = move _11 as *const () (FnPtrToPtr); StorageDead(_11); _7 = Eq(move _8, move _10); switchInt(move _7) -> [0: bb2, otherwise: bb1]
-- bb1: StorageDead(_10); StorageDead(_8); _6 = const 1_u32; goto -> bb3
-- bb2: StorageDead(_10); StorageDead(_8); _6 = const 0_u32; goto -> bb3
-- bb3: StorageDead(_7); StorageLive(_12); StorageLive(_13); _13 = copy _4; StorageLive(_14); _14 = copy _1; _12 = move _13(move _14) -> [return: bb4, unwind continue]
-- bb4: StorageDead(_14); StorageDead(_13); StorageLive(_15); StorageLive(_16); _16 = copy _6; _17 = Lt(const 8_u32, const 32_u32); assert(move _17, "attempt to shift left by `{}`, which would overflow", const 8_u32) -> [success: bb5, unwind continue]
-- bb5: _15 = Shl(move _16, const 8_u32); StorageDead(_16); _0 = BitXor(move _12, move _15); StorageDead(_15); StorageDead(_12); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::widen_and_identity",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::widen_and_identity::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "same") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 17), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:55:9: 55:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::widen_and_identity::{closure#0}") List.nil)), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:55:36: 55:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:56:9: 56:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "UnsafeFnPointer") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:57:9: 57:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:57:24: 57:60" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:57:24: 57:40" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:57:25: 57:26" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:57:25: 57:26" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 9, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 })), span := "src/lib.rs:57:24: 57:40" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:57:39: 57:40" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:57:44: 57:60" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:57:45: 57:46" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:57:45: 57:46" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 11, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 })), span := "src/lib.rs:57:44: 57:60" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 8, projection := List.nil }) (Operand.move { local_ := 10, projection := List.nil }))), span := "src/lib.rs:57:24: 57:60" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 7, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:57:24: 57:60" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:57:63: 57:67" } List.nil))), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:57:21: 57:83" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:57:77: 57:81" } List.nil))), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:57:21: 57:83" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:57:82: 57:83" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:58:5: 58:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:58:15: 58:16" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:58:15: 58:16" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:58:17: 58:18" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:58:17: 58:18" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 13, projection := List.nil }) (List.cons (Operand.move { local_ := 14, projection := List.nil }) List.nil) { local_ := 12, projection := List.nil } (Option.some 4) UnwindAction.continue_), span := "src/lib.rs:58:15: 58:19" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:58:18: 58:19" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:58:18: 58:19" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:58:25: 58:39" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:58:26: 58:30" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:58:26: 58:30" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:58:25: 58:39" } List.nil)))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 17, projection := List.nil }) true 5 UnwindAction.continue_), span := "src/lib.rs:58:25: 58:39" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 16, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }))), span := "src/lib.rs:58:25: 58:39" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 12, projection := List.nil }) (Operand.move { local_ := 15, projection := List.nil }))), span := "src/lib.rs:58:5: 58:39" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:59:1: 59:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:59:1: 59:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:59:1: 59:2" } List.nil)))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:59:2: 59:2" }, isCleanup := false } List.nil)))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.widen_and_identity

namespace Mir.ClosureMatrix.widen_and_identity_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::widen_and_identity::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 1_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::widen_and_identity::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::widen_and_identity::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:55:51: 55:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:55:51: 55:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:55:38: 55:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:55:58: 55:59" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:55:59: 55:59" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.widen_and_identity_closure_0

namespace Mir.ClosureMatrix.zero_arg

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::zero_arg`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_1); StorageLive(_2); _2 = {closure@src/lib.rs:40:26: 40:28}; _1 = move _2 as fn() -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_2); StorageLive(_3); _3 = copy _1; _0 = move _3() -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::zero_arg",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::zero_arg::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:40:9: 40:10" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::zero_arg::{closure#0}") List.nil)), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 2, projection := List.nil }) { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:40:27: 40:28" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:41:5: 41:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:41:5: 41:6" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 3, projection := List.nil }) List.nil { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:41:5: 41:8" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:41:7: 41:8" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:42:1: 42:2" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:42:2: 42:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.zero_arg

namespace Mir.ClosureMatrix.zero_arg_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::zero_arg::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: _0 = const 7_u32; return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::zero_arg::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::zero_arg::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }))), span := "src/lib.rs:40:29: 40:33" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:40:33: 40:33" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.ClosureMatrix.zero_arg_closure_0


/-! ## 3. The closure matrix capture re-targeted at `V2026_08_01` (namespace prefix `V08.`) -/

namespace V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::<Guard as core::ops::Drop>::drop`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=4, align=4
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: _0 = const (); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::<Guard as core::ops::Drop>::drop",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "core::ops::Drop::drop", args := (List.cons (RigidTy.adt "closure_matrix::Guard" List.nil) List.nil) }, implPath := "closure_matrix::<Guard as core::ops::Drop>::drop" } List.nil),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.adt "closure_matrix::Guard" List.nil)), layoutIdx := 3 }, debugName := (Option.some "self") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:80:24: 80:26" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:80:26: 80:26" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop

namespace V08.Mir.ClosureMatrix.call_generic

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::call_generic`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: StorageLive(_2); _2 = copy _1; _0 = generic_closure::<u32>(move _2) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::call_generic",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:109:28: 109:29" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:109:28: 109:29" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::generic_closure" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 2, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:109:5: 109:30" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:109:29: 109:30" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:110:2: 110:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.call_generic

namespace V08.Mir.ClosureMatrix.capturing_direct

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::capturing_direct`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=4, align=4
-- TypeLayout[3]: size=0, align=1
-- TypeLayout[4]: size=8, align=8
-- TypeLayout[5]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) } List.nil)))))) }

-- bb0: StorageLive(_3); _3 = (); StorageLive(_4); _4 = {closure@src/lib.rs:114:17: 114:30} { y: copy _2 }; StorageLive(_5); _5 = {closure@src/lib.rs:115:15: 115:28} { unit: copy _3 }; StorageLive(_6); StorageLive(_7); _7 = &_4; StorageLive(_8); StorageLive(_9); _9 = copy _1; _8 = (move _9,); _6 = <{closure@src/lib.rs:114:17: 114:30} as core::ops::Fn<(u32,)>>::call(move _7, move _8) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_9); StorageDead(_8); StorageDead(_7); StorageLive(_10); StorageLive(_11); _11 = &_5; StorageLive(_12); StorageLive(_13); _13 = copy _1; _12 = (move _13,); _10 = <{closure@src/lib.rs:115:15: 115:28} as core::ops::Fn<(u32,)>>::call(move _11, move _12) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_13); StorageDead(_12); StorageDead(_11); _0 = BitXor(move _6, move _10); StorageDead(_10); StorageDead(_6); StorageDead(_5); StorageDead(_4); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := (Option.some "unit") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := (Option.some "add_y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil)), layoutIdx := 3 }, debugName := (Option.some "zst") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:113:9: 113:13" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple List.nil)), span := "src/lib.rs:113:16: 113:18" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:114:9: 114:14" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::capturing_direct::{closure#0}") (List.cons (Operand.copy { local_ := 2, projection := List.nil }) List.nil))), span := "src/lib.rs:114:17: 114:49" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:115:9: 115:12" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::capturing_direct::{closure#1}") (List.cons (Operand.copy { local_ := 3, projection := List.nil }) List.nil))), span := "src/lib.rs:115:15: 118:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:119:5: 119:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:119:5: 119:10" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 4, projection := List.nil })), span := "src/lib.rs:119:5: 119:10" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:119:5: 119:13" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:119:11: 119:12" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:119:11: 119:12" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 9, projection := List.nil }) List.nil))), span := "src/lib.rs:119:5: 119:13" } List.nil))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil)) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil)) { local_ := 6, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:119:5: 119:13" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:119:12: 119:13" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:119:16: 119:22" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:119:16: 119:19" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 5, projection := List.nil })), span := "src/lib.rs:119:16: 119:19" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:119:16: 119:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:119:20: 119:21" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:119:20: 119:21" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 13, projection := List.nil }) List.nil))), span := "src/lib.rs:119:16: 119:22" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil)) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 11, projection := List.nil }) (List.cons (Operand.move { local_ := 12, projection := List.nil }) List.nil)) { local_ := 10, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:119:16: 119:22" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 6, projection := List.nil }) (Operand.move { local_ := 10, projection := List.nil }))), span := "src/lib.rs:119:5: 119:22" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:119:21: 119:22" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:120:1: 120:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:120:1: 120:2" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:120:1: 120:2" } List.nil))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:120:2: 120:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.capturing_direct

namespace V08.Mir.ClosureMatrix.capturing_direct_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::capturing_direct::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; StorageLive(_4); _4 = copy ((*_1).0: u32); _0 = Add(move _3, move _4); StorageDead(_4); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#0}" (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:114:44: 114:45" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:114:44: 114:45" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:114:47: 114:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:114:47: 114:48" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.move { local_ := 4, projection := List.nil }))), span := "src/lib.rs:114:31: 114:49" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:114:48: 114:49" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:114:48: 114:49" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:114:49: 114:49" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.capturing_direct_closure_0

namespace V08.Mir.ClosureMatrix.capturing_direct_closure_1

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::capturing_direct::{closure#1}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil)))) }

-- bb0: StorageLive(_3); _3 = copy ((*_1).0: ()); _0 = copy _2; StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::capturing_direct::{closure#1}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::capturing_direct::{closure#1}" (List.cons (RigidTy.tuple List.nil) List.nil))), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := (Option.some "_keep") } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:116:13: 116:18" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }) List.nil)) }))), span := "src/lib.rs:116:21: 116:25" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:117:9: 117:10" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:118:5: 118:6" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:118:6: 118:6" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.capturing_direct_closure_1

namespace V08.Mir.ClosureMatrix.ces_through_closure_fn_ptr

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::ces_through_closure_fn_ptr`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:99:30: 99:38}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = (move _5,); StorageDead(_5); StorageLive(_6); _6 = copy _2; _0 = move _6(move (_4.0: u32)) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::ces_through_closure_fn_ptr",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "rt") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:99:9: 99:11" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}") List.nil)), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:99:30: 99:61" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:99:37: 99:38" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:100:23: 100:27" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:100:24: 100:25" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:100:24: 100:25" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil))), span := "src/lib.rs:100:23: 100:27" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:100:26: 100:27" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:100:37: 100:39" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:100:37: 100:39" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:100:5: 100:40" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:100:39: 100:40" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:100:39: 100:40" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:101:1: 101:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:101:2: 101:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.ces_through_closure_fn_ptr

namespace V08.Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::ces_through_closure_fn_ptr::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::ces_through_closure_fn_ptr::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::ces_through_closure_fn_ptr::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:99:52: 99:53" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:99:52: 99:53" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:99:39: 99:61" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:99:60: 99:61" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:99:61: 99:61" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0

namespace V08.Mir.ClosureMatrix.ct_add

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::ct_add`. -/

-- TypeLayout[0]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = copy _1; return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::ct_add",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:95:5: 95:6" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:96:2: 96:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.ct_add

namespace V08.Mir.ClosureMatrix.direct_closure_call

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::direct_closure_call`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil)))) }

-- bb0: StorageLive(_2); _2 = {closure@src/lib.rs:90:13: 90:21}; StorageLive(_3); _3 = &_2; StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = (move _5,); _0 = <{closure@src/lib.rs:90:13: 90:21} as core::ops::Fn<(u32,)>>::call(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::direct_closure_call",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:90:9: 90:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::direct_closure_call::{closure#0}") List.nil)), span := "src/lib.rs:90:13: 90:43" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:91:5: 91:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:91:5: 91:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:91:5: 91:9" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:91:7: 91:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:91:7: 91:8" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil))), span := "src/lib.rs:91:5: 91:9" } List.nil)))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::ops::Fn::call" (List.cons (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil) (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) List.nil)) List.nil))), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:91:5: 91:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:91:8: 91:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:92:1: 92:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:92:2: 92:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.direct_closure_call

namespace V08.Mir.ClosureMatrix.direct_closure_call_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::direct_closure_call::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 9_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::direct_closure_call::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::direct_closure_call::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:90:35: 90:36" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:90:35: 90:36" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 9, sizeBytes := 4 })) }))), span := "src/lib.rs:90:22: 90:43" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:90:42: 90:43" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:90:43: 90:43" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.direct_closure_call_closure_0

namespace V08.Mir.ClosureMatrix.diverging_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::diverging_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } List.nil))))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:73:27: 73:35}; _2 = move _3 as fn(u32) -> ! (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _1; _4 = Eq(move _5, const 0_u32); switchInt(move _4) -> [0: bb2, otherwise: bb1]
-- bb1: StorageDead(_5); StorageLive(_6); StorageLive(_7); _7 = copy _2; StorageLive(_8); _8 = copy _1; _6 = move _7(move _8) -> unwind continue
-- bb2: StorageDead(_5); _0 = copy _1; StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::diverging_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) RigidTy.never Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::diverging_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) RigidTy.never Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:73:9: 73:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:73:27: 73:62" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::diverging_closure::{closure#0}") List.nil)), span := "src/lib.rs:73:27: 73:62" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) RigidTy.never Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:73:27: 73:62" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:73:34: 73:35" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:74:8: 74:17" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:74:8: 74:9" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:74:8: 74:9" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:74:8: 74:17" } List.nil))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 4, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:74:8: 74:17" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:74:16: 74:17" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:74:20: 74:24" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:74:20: 74:21" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:74:20: 74:21" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:74:22: 74:23" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:74:22: 74:23" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil) { local_ := 6, projection := List.nil } Option.none UnwindAction.continue_), span := "src/lib.rs:74:20: 74:24" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:74:16: 74:17" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:74:34: 74:35" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:74:36: 74:37" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:75:1: 75:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:75:2: 75:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.diverging_closure

namespace V08.Mir.ClosureMatrix.diverging_closure_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::diverging_closure::{closure#0}`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=4, align=4
-- TypeLayout[4]: size=8, align=8
-- TypeLayout[5]: size=8, align=8
-- TypeLayout[6]: size=16, align=8
-- TypeLayout[7]: size=16, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 4 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 5 (List.cons 5 List.nil)) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = core::fmt::Arguments::<'_>::from_str(const "closure diverged") -> [return: bb1, unwind continue]
-- bb1: _3 = core::panicking::panic_fmt(move _4) -> unwind continue
def body : CapturedMir :=
  {
    defPath := "closure_matrix::diverging_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::diverging_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 3 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.never, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::fmt::Arguments" List.nil), layoutIdx := 6 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" } (List.cons { kind := (StatementKind.storageLive 4), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::fmt::Arguments::<'a>::from_str" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 7 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 16) }) List.nil) { local_ := 4, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::panicking::panic_fmt" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil) { local_ := 3, projection := List.nil } Option.none UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := (List.cons { allocId := 1, bytes := (List.cons (Option.some (UInt8.ofNat 99)) (List.cons (Option.some (UInt8.ofNat 108)) (List.cons (Option.some (UInt8.ofNat 111)) (List.cons (Option.some (UInt8.ofNat 115)) (List.cons (Option.some (UInt8.ofNat 117)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 32)) (List.cons (Option.some (UInt8.ofNat 100)) (List.cons (Option.some (UInt8.ofNat 105)) (List.cons (Option.some (UInt8.ofNat 118)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 103)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 100)) List.nil)))))))))))))))), relocations := List.nil, align := { bytes := 1 }, mutability := Mutability.not } List.nil)
  }


end V08.Mir.ClosureMatrix.diverging_closure_closure_0

namespace V08.Mir.ClosureMatrix.fn_mut_kind

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_mut_kind`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:28:20: 28:28}; _2 = id_mut::<{closure@src/lib.rs:28:20: 28:28}>(move _3) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_7); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_mut_kind",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:28:9: 28:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:20: 28:50" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_mut_kind::{closure#0}") List.nil)), span := "src/lib.rs:28:20: 28:50" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::id_mut" (List.cons (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil) { local_ := 2, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:28:13: 28:51" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:50: 28:51" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:29:9: 29:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:29:29: 29:30" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:30:5: 30:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:30:5: 30:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:30:7: 30:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:30:7: 30:8" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:30:5: 30:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:30:8: 30:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:30:8: 30:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:31:1: 31:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:31:1: 31:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:31:2: 31:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.fn_mut_kind

namespace V08.Mir.ClosureMatrix.fn_mut_kind_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_mut_kind::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 2_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_mut_kind::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.closure "closure_matrix::fn_mut_kind::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:42: 28:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:28:42: 28:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:28:29: 28:50" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:49: 28:50" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:28:50: 28:50" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.fn_mut_kind_closure_0

namespace V08.Mir.ClosureMatrix.fn_once_kind

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_once_kind`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:34:21: 34:29}; _2 = id_once::<{closure@src/lib.rs:34:21: 34:29}>(move _3) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_7); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_once_kind",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := (Option.some "c") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:34:9: 34:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:34:21: 34:51" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_once_kind::{closure#0}") List.nil)), span := "src/lib.rs:34:21: 34:51" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::id_once" (List.cons (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil) List.nil)), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil) { local_ := 2, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:34:13: 34:52" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:34:51: 34:52" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:35:9: 35:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:35:29: 35:30" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:36:5: 36:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:36:5: 36:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:36:7: 36:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:36:7: 36:8" } List.nil)))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:36:5: 36:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:36:8: 36:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:36:8: 36:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:37:1: 37:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:37:1: 37:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:37:2: 37:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.fn_once_kind

namespace V08.Mir.ClosureMatrix.fn_once_kind_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_once_kind::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 3_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_once_kind::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_once_kind::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:34:43: 34:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:34:43: 34:44" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:34:30: 34:51" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:34:50: 34:51" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:34:51: 34:51" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.fn_once_kind_closure_0

namespace V08.Mir.ClosureMatrix.fn_shared

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_shared`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:23:29: 23:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_shared",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::fn_shared::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:23:9: 23:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::fn_shared::{closure#0}") List.nil)), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:23:29: 23:60" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:36: 23:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:24:5: 24:6" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:24:5: 24:6" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:24:7: 24:8" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:24:7: 24:8" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:24:5: 24:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:24:8: 24:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:24:8: 24:9" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:25:1: 25:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:25:2: 25:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.fn_shared

namespace V08.Mir.ClosureMatrix.fn_shared_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::fn_shared::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::fn_shared::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::fn_shared::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:23:51: 23:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:23:51: 23:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:23:38: 23:60" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:59: 23:60" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:23:60: 23:60" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.fn_shared_closure_0

namespace V08.Mir.ClosureMatrix.generic_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::generic_closure`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:104:25: 104:31}; _2 = move _3 as fn(T) -> T (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.generic_closure

namespace V08.Mir.ClosureMatrix.generic_closure_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::generic_closure::{closure#0}`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: _0 = copy _2; return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.generic_closure_closure_0

namespace V08.Mir.ClosureMatrix.helper_triple

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::helper_triple`. -/

-- TypeLayout[0]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: StorageLive(_2); _2 = copy _1; _0 = Mul(move _2, const 3_u32); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::helper_triple",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:19:18: 19:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:19:18: 19:19" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.mul (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:19:5: 19:26" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:19:25: 19:26" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:20:2: 20:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.helper_triple

namespace V08.Mir.ClosureMatrix.id_mut

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::id_mut`. -/

-- TypeLayout[0]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = move _1; return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.id_mut

namespace V08.Mir.ClosureMatrix.id_once

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::id_once`. -/

-- TypeLayout[0]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = move _1; return
def body : CapturedMir :=
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
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.id_once

namespace V08.Mir.ClosureMatrix.mixed_fn_item_and_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::mixed_fn_item_and_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); _2 = helper_triple as fn(u32) -> u32 (PointerCoercion(ReifyFnPointer(Safe), Implicit)); StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:63:29: 63:37}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); StorageLive(_6); _6 = copy _2; StorageLive(_7); _7 = copy _1; _5 = move _6(move _7) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_7); StorageDead(_6); StorageLive(_8); StorageLive(_9); _9 = copy _3; StorageLive(_10); _10 = copy _1; _8 = move _9(move _10) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_10); StorageDead(_9); _0 = BitXor(move _5, move _8); StorageDead(_8); StorageDead(_5); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::mixed_fn_item_and_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:62:9: 62:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ReifyFnPointer(Safe)") (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_matrix::helper_triple" List.nil), layoutIdx := 2 }, val := ConstValue.zeroSized }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:62:29: 62:42" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:63:9: 63:10" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}") List.nil)), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:63:29: 63:59" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:63:36: 63:37" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:64:5: 64:9" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:64:5: 64:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:64:5: 64:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:64:7: 64:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:64:7: 64:8" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 5, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:64:5: 64:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:64:8: 64:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:64:8: 64:9" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:64:12: 64:16" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:64:12: 64:13" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:64:12: 64:13" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:64:14: 64:15" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:64:14: 64:15" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 9, projection := List.nil }) (List.cons (Operand.move { local_ := 10, projection := List.nil }) List.nil) { local_ := 8, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:64:12: 64:16" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 5, projection := List.nil }) (Operand.move { local_ := 8, projection := List.nil }))), span := "src/lib.rs:64:5: 64:16" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:64:15: 64:16" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:65:1: 65:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:65:1: 65:2" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:65:2: 65:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.mixed_fn_item_and_closure

namespace V08.Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::mixed_fn_item_and_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Mul(move _3, const 5_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::mixed_fn_item_and_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::mixed_fn_item_and_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:63:51: 63:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:63:51: 63:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.mul (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:63:38: 63:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:63:58: 63:59" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:63:59: 63:59" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0

namespace V08.Mir.ClosureMatrix.tail_through_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::tail_through_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:68:29: 68:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; StorageLive(_6); _6 = copy _1; tailcall move _5(move _6)
def body : CapturedMir :=
  {
    defPath := "closure_matrix::tail_through_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::tail_through_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:68:9: 68:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::tail_through_closure::{closure#0}") List.nil)), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:68:29: 68:46" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:68:36: 68:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:69:5: 69:16" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:69:12: 69:13" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:69:12: 69:13" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:69:14: 69:15" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:69:14: 69:15" } List.nil)))))))))), terminator := { kind := (TerminatorKind.tailCall (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil)), span := "src/lib.rs:69:5: 69:16" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.tail_through_closure

namespace V08.Mir.ClosureMatrix.tail_through_closure_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::tail_through_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 5_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::tail_through_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::tail_through_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:68:38: 68:39" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:68:38: 68:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }))), span := "src/lib.rs:68:38: 68:46" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:68:45: 68:46" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:68:46: 68:46" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.tail_through_closure_closure_0

namespace V08.Mir.ClosureMatrix.two_arg

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::two_arg`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:45:34: 45:50}; _3 = move _4 as fn(u32, u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); _6 = copy _1; StorageLive(_7); _7 = copy _2; _0 = move _5(move _6, move _7) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_7); StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::two_arg",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "y") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::two_arg::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:45:9: 45:10" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::two_arg::{closure#0}") List.nil)), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) (List.cons (RigidTy.uint UintTy.u32) List.nil)) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:45:34: 45:56" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:45:49: 45:50" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:46:5: 46:6" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:46:5: 46:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:46:7: 46:8" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:46:7: 46:8" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:46:10: 46:11" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:46:10: 46:11" } List.nil))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:46:5: 46:12" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:46:11: 46:12" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:47:1: 47:2" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:47:2: 47:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.two_arg

namespace V08.Mir.ClosureMatrix.two_arg_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::two_arg::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _3; _0 = BitXor(move _4, move _5); StorageDead(_5); StorageDead(_4); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::two_arg::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 3,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::two_arg::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:45:51: 45:52" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:45:51: 45:52" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:45:51: 45:56" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:45:55: 45:56" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:45:55: 45:56" } List.nil))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:45:56: 45:56" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil))), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.two_arg_closure_0

namespace V08.Mir.ClosureMatrix.unsafe_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unsafe_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:50:36: 50:44}; _2 = move _3 as unsafe fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Unsafe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unsafe_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::unsafe_closure::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:50:9: 50:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::unsafe_closure::{closure#0}") List.nil)), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Unsafe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:50:36: 50:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:50:43: 50:44" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:51:14: 51:15" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:51:14: 51:15" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:51:16: 51:17" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:51:16: 51:17" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:51:14: 51:18" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:51:17: 51:18" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:51:17: 51:18" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:52:1: 52:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:52:2: 52:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.unsafe_closure

namespace V08.Mir.ClosureMatrix.unsafe_closure_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unsafe_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 17_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unsafe_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::unsafe_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:50:45: 50:46" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:50:45: 50:46" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 17, sizeBytes := 4 })) }))), span := "src/lib.rs:50:45: 50:54" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:50:53: 50:54" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:50:54: 50:54" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.unsafe_closure_closure_0

namespace V08.Mir.ClosureMatrix.unwind_through_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unwind_through_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = copy _1; _2 = Guard(move _3); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = {closure@src/lib.rs:85:29: 85:37}; _4 = move _5 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_5); StorageLive(_6); _6 = copy _4; StorageLive(_7); _7 = copy _1; _0 = move _6(move _7) -> [return: bb1, unwind: bb3]
-- bb1: StorageDead(_7); StorageDead(_6); StorageDead(_4); drop(_2) -> [return: bb2, unwind: bb4]
-- bb2: StorageDead(_2); return
-- bb3: drop(_2) -> [return: bb4, unwind terminate(cleanup)]
-- bb4: resume
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unwind_through_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_matrix::Guard" List.nil), layoutIdx := 1 }, debugName := (Option.some "_g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::unwind_through_closure::{closure#0}" List.nil), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:84:9: 84:11" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:84:20: 84:21" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:84:20: 84:21" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_matrix::Guard" 0 Option.none) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil))), span := "src/lib.rs:84:14: 84:22" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:84:21: 84:22" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:85:9: 85:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::unwind_through_closure::{closure#0}") List.nil)), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 2 })), span := "src/lib.rs:85:29: 85:80" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:85:36: 85:37" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:86:5: 86:6" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:86:5: 86:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:86:7: 86:8" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:86:7: 86:8" } List.nil)))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 6, projection := List.nil }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) (UnwindAction.cleanup 3)), span := "src/lib.rs:86:5: 86:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:86:8: 86:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:86:8: 86:9" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:87:1: 87:2" } List.nil))), terminator := { kind := (TerminatorKind.drop { local_ := 2, projection := List.nil } 2 (UnwindAction.cleanup 4)), span := "src/lib.rs:87:1: 87:2" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:87:1: 87:2" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:87:2: 87:2" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.drop { local_ := 2, projection := List.nil } 4 UnwindAction.terminate), span := "src/lib.rs:87:1: 87:2" }, isCleanup := true } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unwindResume, span := "src/lib.rs:83:1: 87:2" }, isCleanup := true } List.nil))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.unwind_through_closure

namespace V08.Mir.ClosureMatrix.unwind_through_closure_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::unwind_through_closure::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=0, align=1
-- TypeLayout[5]: size=8, align=8
-- TypeLayout[6]: size=8, align=8
-- TypeLayout[7]: size=16, align=8
-- TypeLayout[8]: size=16, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 5 List.nil) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 6 (List.cons 6 List.nil)) } (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; _3 = Eq(move _4, const 0_u32); switchInt(move _3) -> [0: bb3, otherwise: bb1]
-- bb1: StorageDead(_4); StorageLive(_6); StorageLive(_7); _7 = core::fmt::Arguments::<'_>::from_str(const "zero") -> [return: bb2, unwind continue]
-- bb2: _6 = core::panicking::panic_fmt(move _7) -> unwind continue
-- bb3: StorageDead(_4); _0 = copy _2; StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::unwind_through_closure::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::unwind_through_closure::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.never, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::fmt::Arguments" List.nil), layoutIdx := 7 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:85:41: 85:50" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:85:41: 85:42" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:85:41: 85:42" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 4, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:85:41: 85:50" } List.nil)))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 1 }), span := "src/lib.rs:85:41: 85:50" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:85:49: 85:50" } (List.cons { kind := (StatementKind.storageLive 6), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" } (List.cons { kind := (StatementKind.storageLive 7), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::fmt::Arguments::<'a>::from_str" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 8 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 4) }) List.nil) { local_ := 7, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:38: 62:72" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::panicking::panic_fmt" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) List.nil) { local_ := 6, projection := List.nil } Option.none UnwindAction.continue_), span := "/rustc/library/core/src/panic.rs:62:9: 62:73" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:85:49: 85:50" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:85:77: 85:78" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:85:79: 85:80" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:85:80: 85:80" }, isCleanup := false } List.nil)))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := (List.cons { allocId := 1, bytes := (List.cons (Option.some (UInt8.ofNat 122)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 114)) (List.cons (Option.some (UInt8.ofNat 111)) List.nil)))), relocations := List.nil, align := { bytes := 1 }, mutability := Mutability.not } List.nil)
  }


end V08.Mir.ClosureMatrix.unwind_through_closure_closure_0

namespace V08.Mir.ClosureMatrix.widen_and_identity

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::widen_and_identity`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil))))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:55:29: 55:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as unsafe fn(u32) -> u32 (PointerCoercion(UnsafeFnPointer, Implicit)); StorageDead(_5); StorageLive(_6); StorageLive(_7); StorageLive(_8); StorageLive(_9); _9 = copy _2; _8 = move _9 as *const () (FnPtrToPtr); StorageDead(_9); StorageLive(_10); StorageLive(_11); _11 = copy _4; _10 = move _11 as *const () (FnPtrToPtr); StorageDead(_11); _7 = Eq(move _8, move _10); switchInt(move _7) -> [0: bb2, otherwise: bb1]
-- bb1: StorageDead(_10); StorageDead(_8); _6 = const 1_u32; goto -> bb3
-- bb2: StorageDead(_10); StorageDead(_8); _6 = const 0_u32; goto -> bb3
-- bb3: StorageDead(_7); StorageLive(_12); StorageLive(_13); _13 = copy _4; StorageLive(_14); _14 = copy _1; _12 = move _13(move _14) -> [return: bb4, unwind continue]
-- bb4: StorageDead(_14); StorageDead(_13); StorageLive(_15); StorageLive(_16); _16 = copy _6; _17 = Lt(const 8_u32, const 32_u32); assert(move _17, "attempt to shift left by `{}`, which would overflow", const 8_u32) -> [success: bb5, unwind continue]
-- bb5: _15 = Shl(move _16, const 8_u32); StorageDead(_16); _0 = BitXor(move _12, move _15); StorageDead(_15); StorageDead(_12); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::widen_and_identity",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::widen_and_identity::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "same") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } List.nil)))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 17), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:55:9: 55:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::widen_and_identity::{closure#0}") List.nil)), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:55:29: 55:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:55:36: 55:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:56:9: 56:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "UnsafeFnPointer") (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.unsafe_ CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:56:36: 56:37" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:57:9: 57:13" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:57:24: 57:60" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:57:24: 57:40" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:57:25: 57:26" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:57:25: 57:26" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 9, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 })), span := "src/lib.rs:57:24: 57:40" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:57:39: 57:40" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:57:44: 57:60" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:57:45: 57:46" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:57:45: 57:46" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 11, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 4 })), span := "src/lib.rs:57:44: 57:60" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.move { local_ := 8, projection := List.nil }) (Operand.move { local_ := 10, projection := List.nil }))), span := "src/lib.rs:57:24: 57:60" } List.nil)))))))))))))))))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 7, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:57:24: 57:60" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:57:63: 57:67" } List.nil))), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:57:21: 57:83" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:57:59: 57:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }))), span := "src/lib.rs:57:77: 57:81" } List.nil))), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:57:21: 57:83" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:57:82: 57:83" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:58:5: 58:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:58:15: 58:16" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:58:15: 58:16" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:58:17: 58:18" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:58:17: 58:18" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 13, projection := List.nil }) (List.cons (Operand.move { local_ := 14, projection := List.nil }) List.nil) { local_ := 12, projection := List.nil } (Option.some 4) UnwindAction.continue_), span := "src/lib.rs:58:15: 58:19" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:58:18: 58:19" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:58:18: 58:19" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:58:25: 58:39" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:58:26: 58:30" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:58:26: 58:30" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 32, sizeBytes := 4 })) }))), span := "src/lib.rs:58:25: 58:39" } List.nil)))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 17, projection := List.nil }) true 5 UnwindAction.continue_), span := "src/lib.rs:58:25: 58:39" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.binaryOp BinOp.shl (Operand.move { local_ := 16, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 8, sizeBytes := 4 })) }))), span := "src/lib.rs:58:25: 58:39" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 12, projection := List.nil }) (Operand.move { local_ := 15, projection := List.nil }))), span := "src/lib.rs:58:5: 58:39" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:58:38: 58:39" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:59:1: 59:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:59:1: 59:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:59:1: 59:2" } List.nil)))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:59:2: 59:2" }, isCleanup := false } List.nil)))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.widen_and_identity

namespace V08.Mir.ClosureMatrix.widen_and_identity_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::widen_and_identity::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = Add(move _3, const 1_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::widen_and_identity::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::widen_and_identity::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:55:51: 55:52" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:55:51: 55:52" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.add (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:55:38: 55:59" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:55:58: 55:59" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:55:59: 55:59" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.widen_and_identity_closure_0

namespace V08.Mir.ClosureMatrix.zero_arg

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::zero_arg`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_1); StorageLive(_2); _2 = {closure@src/lib.rs:40:26: 40:28}; _1 = move _2 as fn() -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_2); StorageLive(_3); _3 = copy _1; _0 = move _3() -> [return: bb1, unwind continue]
-- bb1: StorageDead(_3); StorageDead(_1); return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::zero_arg",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_matrix::zero_arg::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:40:9: 40:10" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_matrix::zero_arg::{closure#0}") List.nil)), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 2, projection := List.nil }) { kind := (RigidTy.fnPtr List.nil (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:40:26: 40:33" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:40:27: 40:28" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:41:5: 41:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:41:5: 41:6" } List.nil))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 3, projection := List.nil }) List.nil { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:41:5: 41:8" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:41:7: 41:8" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:42:1: 42:2" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:42:2: 42:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.zero_arg

namespace V08.Mir.ClosureMatrix.zero_arg_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_matrix::zero_arg::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: _0 = const 7_u32; return
def body : CapturedMir :=
  {
    defPath := "closure_matrix::zero_arg::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_matrix::zero_arg::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }))), span := "src/lib.rs:40:29: 40:33" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:40:33: 40:33" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }


end V08.Mir.ClosureMatrix.zero_arg_closure_0


/-! ## 3b. Verbatim `rustc-capture` output: nested, trait-impl, and transmute closures (`V2026_06_01`) -/

namespace Mir.ClosureExtended.BoxedVal_as_Compute_compute

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::<BoxedVal as Compute>::compute`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=0, align=1
-- TypeLayout[5]: size=1, align=1
-- TypeLayout[6]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 5 List.nil)) } List.nil))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:21:33: 21:41}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); StorageLive(_7); _7 = copy _2; StorageLive(_8); _8 = copy ((*_1).0: u32); _9 = AddWithOverflow(copy _7, copy _8); assert(!move (_9.1: bool), "attempt to compute `{} + {}`, which would overflow", move _7, move _8) -> [success: bb1, unwind continue]
-- bb1: _6 = move (_9.0: u32); StorageDead(_8); StorageDead(_7); _0 = move _5(move _6) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::<BoxedVal as Compute>::compute",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "closure_extended::Compute::compute", args := (List.cons (RigidTy.adt "closure_extended::BoxedVal" List.nil) List.nil) }, implPath := "closure_extended::<BoxedVal as Compute>::compute" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "closure_extended::BoxedVal" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::<BoxedVal as Compute>::compute::{closure#0}" List.nil), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 6 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 9), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:21:13: 21:14" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:21:33: 21:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::<BoxedVal as Compute>::compute::{closure#0}") List.nil)), span := "src/lib.rs:21:33: 21:48" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 })), span := "src/lib.rs:21:33: 21:48" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:21:40: 21:41" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:22:9: 22:10" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:22:9: 22:10" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:22:11: 22:21" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:22:11: 22:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:22:11: 22:12" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:22:15: 22:21" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:22:15: 22:21" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 7, projection := List.nil }) (Operand.copy { local_ := 8, projection := List.nil }))), span := "src/lib.rs:22:11: 22:21" } List.nil)))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 9, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 5 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:22:11: 22:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.move { local_ := 9, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:22:11: 22:21" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:22:20: 22:21" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:22:20: 22:21" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:22:9: 22:22" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:22:21: 22:22" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:22:21: 22:22" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:5: 23:6" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:23:6: 23:6" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.BoxedVal_as_Compute_compute

namespace Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::<BoxedVal as Compute>::compute::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 19_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::<BoxedVal as Compute>::compute::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::<BoxedVal as Compute>::compute::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:21:42: 21:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:21:42: 21:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 19, sizeBytes := 4 })) }))), span := "src/lib.rs:21:42: 21:48" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:21:47: 21:48" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:21:48: 21:48" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0

namespace Mir.ClosureExtended.Compute_compute_default

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::Compute::compute_default`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=0, align=1
-- TypeLayout[5]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:12:33: 12:41}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); StorageLive(_7); _7 = &(*_1); StorageLive(_8); _8 = copy _2; _6 = <Self as Compute>::compute(move _7, move _8) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_8); StorageDead(_7); _0 = move _5(move _6) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::Compute::compute_default",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "Self" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.param 0 "Self")), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::Compute::compute_default::{closure#0}" List.nil), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.param 0 "Self")), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } List.nil))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:12:13: 12:14" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:12:33: 12:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::Compute::compute_default::{closure#0}") List.nil)), span := "src/lib.rs:12:33: 12:48" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 })), span := "src/lib.rs:12:33: 12:48" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:12:40: 12:41" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:13:9: 13:10" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:13:9: 13:10" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:13:11: 13:26" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:13:11: 13:15" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:13:11: 13:15" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:13:24: 13:25" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:13:24: 13:25" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_extended::Compute::compute" (List.cons (RigidTy.param 0 "Self") List.nil)), layoutIdx := 5 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil)) { local_ := 6, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:13:11: 13:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:13:25: 13:26" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:13:25: 13:26" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:13:9: 13:27" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:13:26: 13:27" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:13:26: 13:27" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:14:5: 14:6" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:14:6: 14:6" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.Compute_compute_default

namespace Mir.ClosureExtended.Compute_compute_default_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::Compute::compute_default::{closure#0}`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=1, align=1
-- TypeLayout[5]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 (List.cons 4 List.nil)) } List.nil)))))) }

-- bb0: StorageLive(_3); _3 = copy _2; _4 = AddWithOverflow(copy _3, const 11_u32); assert(!move (_4.1: bool), "attempt to compute `{} + {}`, which would overflow", move _3, const 11_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = move (_4.0: u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::Compute::compute_default::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "Self" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::Compute::compute_default::{closure#0}" List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 5 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:12:42: 12:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:12:42: 12:43" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 11, sizeBytes := 4 })) }))), span := "src/lib.rs:12:42: 12:48" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 4 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:12:42: 12:48" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }) List.nil) }))), span := "src/lib.rs:12:42: 12:48" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:12:47: 12:48" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:12:48: 12:48" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.Compute_compute_default_closure_0

namespace Mir.ClosureExtended.call_concrete_trait_impl

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::call_concrete_trait_impl`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); _2 = BoxedVal(const 5_u32); StorageLive(_3); _3 = &_2; StorageLive(_4); _4 = copy _1; _0 = <BoxedVal as Compute>::compute(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::call_concrete_trait_impl",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_extended::BoxedVal" List.nil), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "closure_extended::BoxedVal" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:27:9: 27:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_extended::BoxedVal" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }) List.nil))), span := "src/lib.rs:27:13: 27:24" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:5: 28:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:28:5: 28:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:28:15: 28:16" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:28:15: 28:16" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_extended::Compute::compute" (List.cons (RigidTy.adt "closure_extended::BoxedVal" List.nil) List.nil)), layoutIdx := 3 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:28:5: 28:17" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:28:16: 28:17" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:16: 28:17" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:29:1: 29:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:29:2: 29:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.call_concrete_trait_impl

namespace Mir.ClosureExtended.call_default_trait_closure

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::call_default_trait_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); _2 = BoxedVal(const 5_u32); StorageLive(_3); _3 = &_2; StorageLive(_4); _4 = copy _1; _0 = <BoxedVal as Compute>::compute_default(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::call_default_trait_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_extended::BoxedVal" List.nil), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "closure_extended::BoxedVal" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:32:9: 32:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_extended::BoxedVal" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }) List.nil))), span := "src/lib.rs:32:13: 32:24" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:33:5: 33:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:33:5: 33:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:33:23: 33:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:33:23: 33:24" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_extended::Compute::compute_default" (List.cons (RigidTy.adt "closure_extended::BoxedVal" List.nil) List.nil)), layoutIdx := 3 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:33:5: 33:25" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:33:24: 33:25" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:33:24: 33:25" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:34:1: 34:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:34:2: 34:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.call_default_trait_closure

namespace Mir.ClosureExtended.fn_ptr_transmute_roundtrip

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::fn_ptr_transmute_roundtrip`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:37:29: 37:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as *const () (FnPtrToPtr); StorageDead(_5); StorageLive(_6); StorageLive(_7); _7 = copy _4; _6 = move _7 as fn(u32) -> u32 (Transmute); StorageDead(_7); StorageLive(_8); _8 = copy _6; StorageLive(_9); _9 = copy _1; _0 = move _8(move _9) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_9); StorageDead(_8); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::fn_ptr_transmute_roundtrip",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := (Option.some "raw") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:37:9: 37:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:37:29: 37:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}") List.nil)), span := "src/lib.rs:37:29: 37:44" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:37:29: 37:44" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:37:36: 37:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:38:9: 38:12" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:38:26: 38:27" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:38:26: 38:27" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 })), span := "src/lib.rs:38:26: 38:40" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:38:39: 38:40" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:39:9: 39:10" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:39:59: 39:62" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:39:59: 39:62" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 7, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:39:38: 39:63" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:39:62: 39:63" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:40:5: 40:6" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:40:5: 40:6" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:40:7: 40:8" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:40:7: 40:8" } List.nil))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 8, projection := List.nil }) (List.cons (Operand.move { local_ := 9, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:40:5: 40:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:40:8: 40:9" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:40:8: 40:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:41:1: 41:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:41:1: 41:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:41:1: 41:2" } List.nil))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:41:2: 41:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.fn_ptr_transmute_roundtrip

namespace Mir.ClosureExtended.fn_ptr_transmute_roundtrip_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::fn_ptr_transmute_roundtrip::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 31_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:37:38: 37:39" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:37:38: 37:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 31, sizeBytes := 4 })) }))), span := "src/lib.rs:37:38: 37:44" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:37:43: 37:44" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:37:44: 37:44" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.fn_ptr_transmute_roundtrip_closure_0

namespace Mir.ClosureExtended.nested_fnptr

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::nested_fnptr`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:2:33: 2:41}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::nested_fnptr",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "outer") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:2:9: 2:14" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:2:33: 5:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::nested_fnptr::{closure#0}") List.nil)), span := "src/lib.rs:2:33: 5:6" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:2:33: 5:6" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:2:40: 2:41" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:6:5: 6:10" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:6:5: 6:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:6:11: 6:12" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:6:11: 6:12" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:6:5: 6:13" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:6:12: 6:13" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:6:12: 6:13" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:7:1: 7:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:7:2: 7:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.nested_fnptr

namespace Mir.ClosureExtended.nested_fnptr_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::nested_fnptr::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:3:37: 3:45}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); StorageLive(_7); _7 = copy _2; _6 = BitXor(move _7, const 3_u32); StorageDead(_7); _0 = move _5(move _6) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::nested_fnptr::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := (Option.some "inner") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:3:13: 3:18" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:3:37: 3:57" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::nested_fnptr::{closure#0}::{closure#0}") List.nil)), span := "src/lib.rs:3:37: 3:57" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 })), span := "src/lib.rs:3:37: 3:57" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:3:44: 3:45" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:4:9: 4:14" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:4:9: 4:14" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:4:15: 4:20" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:4:15: 4:16" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:4:15: 4:16" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 7, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:4:15: 4:20" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:4:19: 4:20" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:4:9: 4:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:4:20: 4:21" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:4:20: 4:21" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:5:5: 5:6" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:5:6: 5:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.nested_fnptr_closure_0

namespace Mir.ClosureExtended.nested_fnptr_closure_0_closure_0

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::nested_fnptr::{closure#0}::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 3 List.nil)) } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; _3 = BitXor(move _4, const 7_u32); StorageDead(_4); _5 = AddWithOverflow(copy _3, const 1_u32); assert(!move (_5.1: bool), "attempt to compute `{} + {}`, which would overflow", move _3, const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = move (_5.0: u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::nested_fnptr::{closure#0}::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 4 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 5), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:3:46: 3:53" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:3:47: 3:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:3:47: 3:48" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }))), span := "src/lib.rs:3:46: 3:53" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:3:52: 3:53" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:3:46: 3:57" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 5, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 3 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:3:46: 3:57" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 5, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:3:46: 3:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:3:56: 3:57" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:3:57: 3:57" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end Mir.ClosureExtended.nested_fnptr_closure_0_closure_0

/-! ## 3c. Verbatim `rustc-capture` output: nested, trait-impl, and transmute closures (`V2026_08_01`) -/

namespace V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::<BoxedVal as Compute>::compute`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=0, align=1
-- TypeLayout[5]: size=1, align=1
-- TypeLayout[6]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 5 List.nil)) } List.nil))))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:21:33: 21:41}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); StorageLive(_7); _7 = copy _2; StorageLive(_8); _8 = copy ((*_1).0: u32); _9 = AddWithOverflow(copy _7, copy _8); assert(!move (_9.1: bool), "attempt to compute `{} + {}`, which would overflow", move _7, move _8) -> [success: bb1, unwind continue]
-- bb1: _6 = move (_9.0: u32); StorageDead(_8); StorageDead(_7); _0 = move _5(move _6) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::<BoxedVal as Compute>::compute",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    traitImpls := (List.cons { traitRef := { defPath := "closure_extended::Compute::compute", args := (List.cons (RigidTy.adt "closure_extended::BoxedVal" List.nil) List.nil) }, implPath := "closure_extended::<BoxedVal as Compute>::compute" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "closure_extended::BoxedVal" List.nil)), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::<BoxedVal as Compute>::compute::{closure#0}" List.nil), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 6 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 9), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:21:13: 21:14" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:21:33: 21:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::<BoxedVal as Compute>::compute::{closure#0}") List.nil)), span := "src/lib.rs:21:33: 21:48" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 })), span := "src/lib.rs:21:33: 21:48" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:21:40: 21:41" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:22:9: 22:10" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:22:9: 22:10" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:22:11: 22:21" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:22:11: 22:12" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:22:11: 22:12" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:22:15: 22:21" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil)) }))), span := "src/lib.rs:22:15: 22:21" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 7, projection := List.nil }) (Operand.copy { local_ := 8, projection := List.nil }))), span := "src/lib.rs:22:11: 22:21" } List.nil)))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 9, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 5 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:22:11: 22:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.move { local_ := 9, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:22:11: 22:21" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:22:20: 22:21" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:22:20: 22:21" } List.nil))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:22:9: 22:22" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:22:21: 22:22" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:22:21: 22:22" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:23:5: 23:6" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:23:6: 23:6" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute

namespace V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::<BoxedVal as Compute>::compute::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 19_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::<BoxedVal as Compute>::compute::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::<BoxedVal as Compute>::compute::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:21:42: 21:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:21:42: 21:43" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 19, sizeBytes := 4 })) }))), span := "src/lib.rs:21:42: 21:48" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:21:47: 21:48" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:21:48: 21:48" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0

namespace V08.Mir.ClosureExtended.Compute_compute_default

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::Compute::compute_default`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=0, align=1
-- TypeLayout[5]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:12:33: 12:41}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); StorageLive(_7); _7 = &(*_1); StorageLive(_8); _8 = copy _2; _6 = <Self as Compute>::compute(move _7, move _8) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_8); StorageDead(_7); _0 = move _5(move _6) -> [return: bb2, unwind continue]
-- bb2: StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::Compute::compute_default",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "Self" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.param 0 "Self")), layoutIdx := 2 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::Compute::compute_default::{closure#0}" List.nil), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.param 0 "Self")), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } List.nil))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:12:13: 12:14" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:12:33: 12:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::Compute::compute_default::{closure#0}") List.nil)), span := "src/lib.rs:12:33: 12:48" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 })), span := "src/lib.rs:12:33: 12:48" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:12:40: 12:41" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:13:9: 13:10" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:13:9: 13:10" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:13:11: 13:26" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:13:11: 13:15" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) })), span := "src/lib.rs:13:11: 13:15" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:13:24: 13:25" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:13:24: 13:25" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_extended::Compute::compute" (List.cons (RigidTy.param 0 "Self") List.nil)), layoutIdx := 5 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 7, projection := List.nil }) (List.cons (Operand.move { local_ := 8, projection := List.nil }) List.nil)) { local_ := 6, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:13:11: 13:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:13:25: 13:26" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:13:25: 13:26" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 2) UnwindAction.continue_), span := "src/lib.rs:13:9: 13:27" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:13:26: 13:27" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:13:26: 13:27" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:14:5: 14:6" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:14:6: 14:6" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.Compute_compute_default

namespace V08.Mir.ClosureExtended.Compute_compute_default_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::Compute::compute_default::{closure#0}`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=1, align=1
-- TypeLayout[5]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 (List.cons 4 List.nil)) } List.nil)))))) }

-- bb0: StorageLive(_3); _3 = copy _2; _4 = AddWithOverflow(copy _3, const 11_u32); assert(!move (_4.1: bool), "attempt to compute `{} + {}`, which would overflow", move _3, const 11_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = move (_4.0: u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::Compute::compute_default::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    typeParamCount := 1,
    genericParams := (List.cons { idx := 0, name := "Self" } List.nil),
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::Compute::compute_default::{closure#0}" List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := (Option.some "v") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 5 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:12:42: 12:43" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:12:42: 12:43" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 11, sizeBytes := 4 })) }))), span := "src/lib.rs:12:42: 12:48" } List.nil)))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 4 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:12:42: 12:48" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 4, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }) List.nil) }))), span := "src/lib.rs:12:42: 12:48" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:12:47: 12:48" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:12:48: 12:48" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.Compute_compute_default_closure_0

namespace V08.Mir.ClosureExtended.call_concrete_trait_impl

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::call_concrete_trait_impl`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); _2 = BoxedVal(const 5_u32); StorageLive(_3); _3 = &_2; StorageLive(_4); _4 = copy _1; _0 = <BoxedVal as Compute>::compute(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::call_concrete_trait_impl",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_extended::BoxedVal" List.nil), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "closure_extended::BoxedVal" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:27:9: 27:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_extended::BoxedVal" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }) List.nil))), span := "src/lib.rs:27:13: 27:24" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:28:5: 28:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:28:5: 28:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:28:15: 28:16" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:28:15: 28:16" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_extended::Compute::compute" (List.cons (RigidTy.adt "closure_extended::BoxedVal" List.nil) List.nil)), layoutIdx := 3 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:28:5: 28:17" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:28:16: 28:17" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:28:16: 28:17" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:29:1: 29:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:29:2: 29:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.call_concrete_trait_impl

namespace V08.Mir.ClosureExtended.call_default_trait_closure

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::call_default_trait_closure`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_2); _2 = BoxedVal(const 5_u32); StorageLive(_3); _3 = &_2; StorageLive(_4); _4 = copy _1; _0 = <BoxedVal as Compute>::compute_default(move _3, move _4) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_4); StorageDead(_3); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::call_default_trait_closure",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "closure_extended::BoxedVal" List.nil), layoutIdx := 1 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "closure_extended::BoxedVal" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:32:9: 32:10" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "closure_extended::BoxedVal" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 5, sizeBytes := 4 })) }) List.nil))), span := "src/lib.rs:32:13: 32:24" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:33:5: 33:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 2, projection := List.nil })), span := "src/lib.rs:33:5: 33:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:33:23: 33:24" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:33:23: 33:24" } List.nil)))))), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "closure_extended::Compute::compute_default" (List.cons (RigidTy.adt "closure_extended::BoxedVal" List.nil) List.nil)), layoutIdx := 3 }, val := ConstValue.zeroSized }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil)) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:33:5: 33:25" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:33:24: 33:25" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:33:24: 33:25" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:34:1: 34:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:34:2: 34:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.call_default_trait_closure

namespace V08.Mir.ClosureExtended.fn_ptr_transmute_roundtrip

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::fn_ptr_transmute_roundtrip`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } List.nil)))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:37:29: 37:37}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); StorageLive(_5); _5 = copy _2; _4 = move _5 as *const () (FnPtrToPtr); StorageDead(_5); StorageLive(_6); StorageLive(_7); _7 = copy _4; _6 = move _7 as fn(u32) -> u32 (Transmute); StorageDead(_7); StorageLive(_8); _8 = copy _6; StorageLive(_9); _9 = copy _1; _0 = move _8(move _9) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_9); StorageDead(_8); StorageDead(_6); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::fn_ptr_transmute_roundtrip",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "f") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := (Option.some "raw") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "g") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:37:9: 37:10" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:37:29: 37:44" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}") List.nil)), span := "src/lib.rs:37:29: 37:44" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:37:29: 37:44" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:37:36: 37:37" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:38:9: 38:12" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:38:26: 38:27" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:38:26: 38:27" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.cast CastKind.fnPtrToPtr (Operand.move { local_ := 5, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.tuple List.nil)), layoutIdx := 3 })), span := "src/lib.rs:38:26: 38:40" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:38:39: 38:40" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:39:9: 39:10" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:39:59: 39:62" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:39:59: 39:62" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 7, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:39:38: 39:63" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:39:62: 39:63" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:40:5: 40:6" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:40:5: 40:6" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:40:7: 40:8" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:40:7: 40:8" } List.nil))))))))))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 8, projection := List.nil }) (List.cons (Operand.move { local_ := 9, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:40:5: 40:9" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:40:8: 40:9" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:40:8: 40:9" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:41:1: 41:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:41:1: 41:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:41:1: 41:2" } List.nil))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:41:2: 41:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.fn_ptr_transmute_roundtrip

namespace V08.Mir.ClosureExtended.fn_ptr_transmute_roundtrip_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::fn_ptr_transmute_roundtrip::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))) }

-- bb0: StorageLive(_3); _3 = copy _2; _0 = BitXor(move _3, const 31_u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::fn_ptr_transmute_roundtrip::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:37:38: 37:39" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:37:38: 37:39" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 31, sizeBytes := 4 })) }))), span := "src/lib.rs:37:38: 37:44" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:37:43: 37:44" } List.nil)))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:37:44: 37:44" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.fn_ptr_transmute_roundtrip_closure_0

namespace V08.Mir.ClosureExtended.nested_fnptr

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::nested_fnptr`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: StorageLive(_2); StorageLive(_3); _3 = {closure@src/lib.rs:2:33: 2:41}; _2 = move _3 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_3); StorageLive(_4); _4 = copy _2; StorageLive(_5); _5 = copy _1; _0 = move _4(move _5) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_5); StorageDead(_4); StorageDead(_2); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::nested_fnptr",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "x") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := (Option.some "outer") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}" List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:2:9: 2:14" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:2:33: 5:6" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::nested_fnptr::{closure#0}") List.nil)), span := "src/lib.rs:2:33: 5:6" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 1 })), span := "src/lib.rs:2:33: 5:6" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:2:40: 2:41" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:6:5: 6:10" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:6:5: 6:10" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:6:11: 6:12" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:6:11: 6:12" } List.nil))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 4, projection := List.nil }) (List.cons (Operand.move { local_ := 5, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:6:5: 6:13" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:6:12: 6:13" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:6:12: 6:13" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:7:1: 7:2" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:7:2: 7:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.nested_fnptr

namespace V08.Mir.ClosureExtended.nested_fnptr_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::nested_fnptr::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = {closure@src/lib.rs:3:37: 3:45}; _3 = move _4 as fn(u32) -> u32 (PointerCoercion(ClosureFnPointer(Safe), Implicit)); StorageDead(_4); StorageLive(_5); _5 = copy _3; StorageLive(_6); StorageLive(_7); _7 = copy _2; _6 = BitXor(move _7, const 3_u32); StorageDead(_7); _0 = move _5(move _6) -> [return: bb1, unwind continue]
-- bb1: StorageDead(_6); StorageDead(_5); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::nested_fnptr::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "a") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := (Option.some "inner") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}::{closure#0}" List.nil), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:3:13: 3:18" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:3:37: 3:57" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.closure "closure_extended::nested_fnptr::{closure#0}::{closure#0}") List.nil)), span := "src/lib.rs:3:37: 3:57" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast (CastKind.pointerCoercion "ClosureFnPointer(Safe)") (Operand.move { local_ := 4, projection := List.nil }) { kind := (RigidTy.fnPtr (List.cons (RigidTy.uint UintTy.u32) List.nil) (RigidTy.uint UintTy.u32) Safety.safe CallConv.rust), layoutIdx := 3 })), span := "src/lib.rs:3:37: 3:57" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:3:44: 3:45" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:4:9: 4:14" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:4:9: 4:14" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:4:15: 4:20" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:4:15: 4:16" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:4:15: 4:16" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 7, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 4 })) }))), span := "src/lib.rs:4:15: 4:20" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:4:19: 4:20" } List.nil)))))))))))), terminator := { kind := (TerminatorKind.call (Operand.move { local_ := 5, projection := List.nil }) (List.cons (Operand.move { local_ := 6, projection := List.nil }) List.nil) { local_ := 0, projection := List.nil } (Option.some 1) UnwindAction.continue_), span := "src/lib.rs:4:9: 4:21" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:4:20: 4:21" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:4:20: 4:21" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:5:5: 5:6" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:5:6: 5:6" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.nested_fnptr_closure_0

namespace V08.Mir.ClosureExtended.nested_fnptr_closure_0_closure_0

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `closure_extended::nested_fnptr::{closure#0}::{closure#0}`. -/

-- TypeLayout[0]: size=4, align=4
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=8, align=8
-- TypeLayout[3]: size=1, align=1
-- TypeLayout[4]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 3 List.nil)) } List.nil))))) }

-- bb0: StorageLive(_3); StorageLive(_4); _4 = copy _2; _3 = BitXor(move _4, const 7_u32); StorageDead(_4); _5 = AddWithOverflow(copy _3, const 1_u32); assert(!move (_5.1: bool), "attempt to compute `{} + {}`, which would overflow", move _3, const 1_u32) -> [success: bb1, unwind continue]
-- bb1: _0 = move (_5.0: u32); StorageDead(_3); return
def body : CapturedMir :=
  {
    defPath := "closure_extended::nested_fnptr::{closure#0}::{closure#0}",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "closure_extended::nested_fnptr::{closure#0}::{closure#0}" List.nil)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 4 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 5), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:3:46: 3:53" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:3:47: 3:48" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:3:47: 3:48" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 4, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }))), span := "src/lib.rs:3:46: 3:53" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:3:52: 3:53" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 3, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:3:46: 3:57" } List.nil))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 5, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 3 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:3:46: 3:57" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 5, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:3:46: 3:57" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:3:56: 3:57" } List.nil)), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:3:57: 3:57" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

end V08.Mir.ClosureExtended.nested_fnptr_closure_0_closure_0

/-! ## 4. Difftest reproducer: exact `rfl` confirmation (`V2026_06_01`) -/

namespace Anneal.ClosureFnPtrTests.Finding

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.Rustc.V2026_06_01.Lower

-- Synthetic stand-in for the `core::fmt::Arguments` constructor `defPath`,
-- linked only by `miri-difftest` oracle modules. The caller has already
-- evaluated the `&'static str` argument; this body returns that message slice
-- as the constructed `Arguments`, which the caller passes to
-- `core::panicking::panic_fmt`.
open Trusted.Rustc.V2026_06_01.Layout in
def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=
  { defPath := defPath
    phase := MirPhaseTag.runtimePostCleanup
    role := ContractRole.model
    argCount := 1
    localDecls :=
      [{ mutability := Mutability.mut, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none },
       { mutability := Mutability.not, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none }]
    basicBlocks :=
      [{ statements :=
           [{ kind := StatementKind.assign { local_ := 0, projection := [] }
                (Rvalue.use (Operand.copy { local_ := 1, projection := [] })),
              span := "<dummy>" }]
         terminator := { kind := TerminatorKind.return_, span := "<dummy>" }
         isCleanup := false }]
    fnAbi :=
      { args := [{ layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }]
        ret := { layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }
        conv := CallConv.rust
        canUnwind := false }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [{ size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }] }
    allocations := [] }

-- Probe a bounded run for its `MirDiffTag` and the span of the statement or
-- terminator that decided it. A panic reports the span of the step that
-- started unwinding (`unwindOrigin`): the step that first entered a cleanup
-- block, or the panicking step itself when no cleanup block ran. The `resume`
-- that ends a cleanup block carries the span of its whole function.
def activeSpan (body : CapturedMir) (st : MirExecState) : String :=
  let raw :=
    match st with
    | .running s =>
      let cur := s.memory.activeCallee.getD body
      match get? cur.basicBlocks s.frame.blockIdx with
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => stmt.span
        | none => bb.terminator.span
      | none => "none"
    | _ => "none"
  if raw == "" || raw == "<dummy>" then "none" else raw
def isCleanupState (body : CapturedMir) : MirExecState → Bool
  | .running s =>
    match get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | some bb => bb.isCleanup
    | none => false
  | _ => false
def unwindOrigin
    (body : CapturedMir) (origin : Option MirExecState) (st st' : MirExecState) :
    Option MirExecState :=
  match origin with
  | some o => some o
  | none => if !isCleanupState body st && isCleanupState body st' then some st else none
def probeMirDiffExecBoundedFrom
    (fuel : Nat) (body : CapturedMir) (origin : Option MirExecState) (st : MirExecState) :
    MirDiffTag × String :=
  match fuel with
  | 0 => (.outOfFuel, activeSpan body st)
  | fuel' + 1 =>
    match stepMirStatePeriodic fuel' body st with
    | .ret (.normal (.unit, _)) => (.normalUnit, "none")
    | .ret (.normal (.scalar sc, _)) => (.normalScalar sc.bits sc.sizeBytes, "none")
    | .ret (.normal (val, mem)) => ((MirDiffVerdict.normal val mem).toTagWithBody body, "none")
    | .ret .panic => (.panic, activeSpan body (origin.getD st))
    | .ret .abort => (.abort, activeSpan body st)
    | .tau st' => probeMirDiffExecBoundedFrom fuel' body (unwindOrigin body origin st st') st'
    | .vis (.inl (.fail .ub)) _ => (.ub, activeSpan body st)
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeSpan body st)
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeSpan body st)
    | .vis (.inr (.inl _)) k =>
      let st' := k PUnit.unit
      probeMirDiffExecBoundedFrom fuel' body (unwindOrigin body origin st st') st'
    | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeSpan body st)
def probeMirDiffExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : MirDiffTag × String :=
  probeMirDiffExecBoundedFrom fuel body none st

set_option maxRecDepth 100000

/-- Linked callee table as `miri-difftest` builds it once local closure bodies
are captured as `CapturedItemKind::Callee`: the driver, both closure bodies, and
the `core::fmt::Arguments` constructor stubs. -/
def linkedCallees : List CapturedMir :=
  [Mir.MiriDiffCorpus.__anneal_vt_driver_61873.body,
   Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_0.body,
   Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_1.body,
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str_nonconst",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str_nonconst",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::new_const",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::new_const"]

/-- The same table without the closure bodies (closures not captured). -/
def linkedCalleesWithoutClosures : List CapturedMir :=
  [Mir.MiriDiffCorpus.__anneal_vt_driver_61873.body,
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str_nonconst",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str_nonconst",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::new_const",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::new_const"]

/-- The freshly captured driver coerces both closures through their
non-capturing closure types (`ClosureArgs::upvar_tys() = []`). -/
theorem finding_driver_coerces_non_capturing_closure_types :
    (Mir.MiriDiffCorpus.__anneal_vt_driver_61873.body.localDecls.map (fun d => d.ty.kind)).filter
        (fun k => match k with | .closure _ _ => true | _ => false) =
      [.closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}" .nil,
       .closure "miri_diff_corpus::__anneal_vt_driver_61873::{closure#1}" .nil] := by
  rfl

/-- Both closure bodies are non-capturing `Fn` bodies of their own closure type
(`_1 : &{closure}`), so indirect calls enter them with a synthesized
environment. -/
theorem finding_closure_bodies_are_non_capturing_fn_bodies :
    calleeOwnClosureShape? Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_0.body =
      .some (.nonCapturing .sharedRef) ∧
    calleeOwnClosureShape? Mir.MiriDiffCorpus.__anneal_vt_driver_61873_closure_1.body =
      .some (.nonCapturing .sharedRef) ∧
    calleeOwnClosureShape? Mir.MiriDiffCorpus.__anneal_vt_driver_61873.body = .none := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Exact difftest confirmation**: the reproducer returns
`MIRI_PASS:scalar:9147:4`, matching Miri. -/
theorem finding_tag_is_9147 :
    evalMirDiffTagBounded 512
        Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body
        (initMachineStateWithMemoryAndCallees
          Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body
          [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 9147 4 := by
  rfl

/-- The difftest probe (tag and deciding span) agrees: `(.normalScalar 9147 4, "none")`. -/
theorem finding_probe_is_9147 :
    probeMirDiffExecBounded 512
        Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body
        (.running
          (initMachineStateWithMemoryAndCallees
            Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body
            [] emptyMemory linkedCallees)) =
      (MirDiffTag.normalScalar 9147 4, "none") := by
  rfl

/-- Without the closure bodies the coercion succeeds and the first indirect call
is an external call to the closure (never `.ub`). -/
theorem finding_without_closure_bodies_is_external_call :
    probeMirDiffExecBounded 512
        Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body
        (.running
          (initMachineStateWithMemoryAndCallees
            Mir.MiriDiffCorpus.pass_shared_temp_const_raw_ptr_read_and_freeze_retag__b22_c27.body
            [] emptyMemory linkedCalleesWithoutClosures)) =
      (MirDiffTag.externalCall "miri_diff_corpus::__anneal_vt_driver_61873::{closure#0}",
        "src/lib.rs:278:27: 278:46") := by
  rfl

end Anneal.ClosureFnPtrTests.Finding

/-! ## 5. Closure function-pointer matrix on `V2026_06_01` -/

namespace Anneal.ClosureFnPtrTests.V06

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### Harness -/

/-- Outcome of a bounded run of `stepMirState`. -/
inductive RunTag : Type where
  | normalScalar (bits sizeBytes : Nat)
  | normalOther
  | panic
  | abort
  | ub
  | unsupported
  | ext (defPath : String)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Run `body` from `st` for at most `fuel` steps of the trusted stepper
`stepMirState`, through its spine-normalizing wrapper `stepMirStatePeriodic`
(`stepMirStatePeriodic_eq` proves it equal to `stepMirState`), which keeps
closed-term kernel evaluation linear. -/
def run (fuel : Nat) (body : CapturedMir) (st : MirExecState) : RunTag :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match Anneal.Rustc.V2026_06_01.Lower.stepMirStatePeriodic fuel' body st with
    | .ret (.normal (.scalar sc, _)) => .normalScalar sc.bits sc.sizeBytes
    | .ret (.normal _) => .normalOther
    | .ret .panic => .panic
    | .ret .abort => .abort
    | .tau st' => run fuel' body st'
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | .vis (.inl (.fail .outOfFuel)) _ => .outOfFuel
    | .vis (.inr (.inl _)) k => run fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => .ext req.defPath

/-- `run` steps exactly like the trusted `stepMirState`. -/
theorem run_step_eq (fuel' : Nat) (body : CapturedMir) (st : MirExecState) :
    Anneal.Rustc.V2026_06_01.Lower.stepMirStatePeriodic fuel' body st = stepMirState body st :=
  Anneal.Rustc.V2026_06_01.Lower.stepMirStatePeriodic_eq fuel' body st

/-- Root memory linking `callees` and the reified function pointers `fnPtrs`. -/
def memWith (body : CapturedMir) (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) : Memory :=
  { emptyMemory with
    nextAllocId := length body.allocations
    globals := body.allocations
    callees := callees
    traitImpls := body.traitImpls
    fnPtrs := fnPtrs }

/-- Run `body` on `args` with linked `callees` and function pointers `fnPtrs`. -/
def runWith (body : CapturedMir) (args : List Value) (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) : RunTag :=
  run 400 body
    (.running
      { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocalsAux 0 body.localDecls args }
        memory := memWith body callees fnPtrs })

/-- A `u32` value. -/
def u32v (n : Nat) : Value := .scalar ⟨n, 4⟩

-- Synthetic stand-in for the `core::fmt::Arguments` constructor `defPath`,
-- linked only by `miri-difftest` oracle modules. The caller has already
-- evaluated the `&'static str` argument; this body returns that message slice
-- as the constructed `Arguments`, which the caller passes to
-- `core::panicking::panic_fmt`.
def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=
  { defPath := defPath
    phase := MirPhaseTag.runtimePostCleanup
    role := ContractRole.model
    argCount := 1
    localDecls :=
      [{ mutability := Mutability.mut, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none },
       { mutability := Mutability.not, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none }]
    basicBlocks :=
      [{ statements :=
           [{ kind := StatementKind.assign { local_ := 0, projection := [] }
                (Rvalue.use (Operand.copy { local_ := 1, projection := [] })),
              span := "<dummy>" }]
         terminator := { kind := TerminatorKind.return_, span := "<dummy>" }
         isCleanup := false }]
    fnAbi :=
      { args := [{ layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }]
        ret := { layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }
        conv := CallConv.rust
        canUnwind := false }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [{ size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }] }
    allocations := [] }

/-- `core::fmt::Arguments` constructor stubs linked by `miri-difftest`. -/
def fmtStubs : List CapturedMir :=
  [fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::new_const",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::new_const"]

/-- Replace the unwind action of the call terminating `bb0`. -/
def setBb0CallUnwind (b : CapturedMir) (u : UnwindAction) : CapturedMir :=
  match b.basicBlocks with
  | bb :: rest =>
    match bb.terminator.kind with
    | .call f a d t _ =>
      { b with
        basicBlocks :=
          { bb with terminator := { bb.terminator with kind := .call f a d t u } } :: rest }
    | _ => b
  | .nil => b

/-! ### Fixture vocabulary -/

def u32K : RigidTy := .uint .u32
def fnU32 : RigidTy := .fnPtr [u32K] u32K .safe .rust
def ufnU32 : RigidTy := .fnPtr [u32K] u32K .unsafe_ .rust
def sharedPath : String := "closure_matrix::fn_shared::{closure#0}"
def capPath : String := "closure_matrix::capturing_direct::{closure#0}"
def capZstPath : String := "closure_matrix::capturing_direct::{closure#1}"
def genericPath : String := "closure_matrix::generic_closure::{closure#0}"
def sharedClo : RigidTy := .closure sharedPath .nil
def capClo : RigidTy := .closure capPath [u32K]
def capZstClo : RigidTy := .closure capZstPath [.tuple .nil]
def plc (l : Nat) : Place := { local_ := l, projection := .nil }
def decl (k : RigidTy) (idx : Nat) : LocalDecl :=
  { mutability := .mut, ty := { kind := k, layoutIdx := idx }, debugName := .none }
/-- Function-pointer value at synthetic allocation `65536`. -/
def fnPtrVal : Value := .ptr { allocId := 65536, offsetBytes := 0 } 8
/-- Environment value passed explicitly by forged or direct calls. -/
def envScalar : Value := .scalar ⟨1, 8⟩
/-- `FnPtrEntry` at `65536` naming `p` with signature `sig`. -/
def entry (p : String) (sig : RigidTy) : FnPtrEntry :=
  { allocId := 65536, defPath := p, fnSig := .some sig }
def retBlock : BasicBlockData :=
  { statements := .nil, terminator := { kind := .return_, span := "ret" }, isCleanup := false }

/-- `fn(_1 : sigKind, _2 : argKind) -> u32 { _0 = _1(_2) }` -/
def ptrCaller (sigKind : RigidTy) (argKind : RigidTy := u32K) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::ptr_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl sigKind 1, decl argKind 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .call (.copy (plc 1)) [.copy (plc 2)] (plc 0) (.some 1) .continue_
             span := "ptr_call" }
         isCleanup := false },
       retBlock] }

/-- `fn(_1 : sigKind, _2 : envKind, _3 : u32) -> u32 { _0 = _1(_2, _3) }`: a forged
`(N + 1)`-argument call passing the closure environment explicitly. -/
def envPtrCaller (sigKind envKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::env_ptr_caller"
    argCount := 3
    localDecls := [decl u32K 0, decl sigKind 1, decl envKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .call (.copy (plc 1)) [.copy (plc 2), .copy (plc 3)] (plc 0) (.some 1) .continue_
             span := "env_ptr_call" }
         isCleanup := false },
       retBlock] }

/-- `fn(_1 : envKind, _2 : u32) -> u32 { _0 = p(_1, _2) }`: a direct
(`isIndirect = false`) call of the closure body `p` passing its environment. -/
def directEnvCaller (p : String) (envKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::direct_env_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl envKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind :=
               .call (.constant { ty := { kind := .fnDef p .nil, layoutIdx := 2 }, val := .zeroSized })
                 [.copy (plc 1), .copy (plc 2)] (plc 0) (.some 1) .continue_
             span := "direct_env_call" }
         isCleanup := false },
       retBlock] }

/-- The `fn_shared` closure body forged to read the field `(*_1).0` of its
(zero-sized) environment. -/
def forgedEnvReadBody : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared_closure_0.body with
    basicBlocks :=
      [{ statements :=
           [{ kind :=
                .assign (plc 0)
                  (.use (.copy { local_ := 1
                                 projection := [.deref, .field 0 { kind := u32K, layoutIdx := 0 }] }))
              span := "forged_env_read" }]
         terminator := { kind := .return_, span := "ret" }
         isCleanup := false }] }

/-- Contrast for `forgedEnvReadBody`: the same forged body reading its argument
`_2` instead of its environment returns normally. -/
def forgedArgReadBody : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared_closure_0.body with
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign (plc 0) (.use (.copy (plc 2))), span := "forged_arg_read" }]
         terminator := { kind := .return_, span := "ret" }
         isCleanup := false }] }

/-- Type arguments of `const_eval_select::<(u32,), ct_add, G, u32>`. -/
def cesTyArgs (rtKind : RigidTy) : List RigidTy :=
  [.tuple [u32K], .fnDef "closure_matrix::ct_add" .nil, rtKind, u32K]

/-- `fn(_1 : u32, _2 : rtKind) -> u32 { StorageLive(_3); _3 = (copy _1,); _0 = const_eval_select(move _3, ct_add, copy _2) }`:
an inline `core::intrinsics::const_eval_select` call with runtime target `_2`. -/
def cesCaller (rtKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::ces_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl u32K 0, decl rtKind 1, decl (.tuple [u32K]) 0]
    basicBlocks :=
      [{ statements :=
           [{ kind := .storageLive 3, span := "ces_live" },
            { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
         terminator :=
           { kind :=
               .call
                 (.constant
                   { ty := { kind := .fnDef "core::intrinsics::const_eval_select" (cesTyArgs rtKind)
                             layoutIdx := 2 }
                     val := .zeroSized })
                 [.move (plc 3),
                  .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                              val := .zeroSized },
                  .copy (plc 2)]
                 (plc 0) (.some 1) .continue_
             span := "ces_call" }
         isCleanup := false },
       retBlock] }

/-- Outcome of `evalReifyFnPointer` on a single operand local. -/
inductive CoerceTag : Type where
  | ok
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Reify local `_0 : opKind` holding `v` to `target` via coercion tag `ck`. -/
def coerce (ck : String) (opKind : RigidTy) (v : Value) (target : RigidTy)
    (callees : List CapturedMir) : CoerceTag :=
  match
    evalReifyFnPointer [.init v] (.move (plc 0)) { kind := target, layoutIdx := 1 }
      { emptyMemory with callees := callees } [decl opKind 2] Mir.ClosureMatrix.fn_shared.layouts ck
  with
  | .ok _ _ _ => .ok
  | .ub => .ub
  | .unsupported => .unsupported

/-- Three-way classification of the captured closure bodies by their own `_1`. -/
theorem closure_shapes :
    (calleeOwnClosureShape? Mir.ClosureMatrix.fn_shared_closure_0.body, calleeOwnClosureShape? Mir.ClosureMatrix.fn_mut_kind_closure_0.body, calleeOwnClosureShape? Mir.ClosureMatrix.fn_once_kind_closure_0.body, calleeOwnClosureShape? Mir.ClosureMatrix.capturing_direct_closure_0.body, calleeOwnClosureShape? Mir.ClosureMatrix.capturing_direct_closure_1.body, calleeOwnClosureShape? Mir.ClosureMatrix.fn_shared.body, calleeOwnClosureShape? Mir.ClosureMatrix.id_mut.body) =
      (.some (.nonCapturing .sharedRef), .some (.nonCapturing .mutRef), .some (.nonCapturing .byValue), .some .capturing, .some .capturing, .none, .none) := by
  rfl

/-- C10 contrast: the unmodified function-pointer check alone would admit the forged `(N + 1)`-argument call; the closure-aware `checkCalleeTargetCompatible` rejects it. -/
theorem forged_env_call_passes_unmodified_fn_ptr_check :
    (checkFnPtrTargetCompatible { defPath := sharedPath, fnSig := .some (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust), isIndirect := true } Mir.ClosureMatrix.fn_shared_closure_0.body 2, checkCalleeTargetCompatible { defPath := sharedPath, fnSig := .some (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust), isIndirect := true } Mir.ClosureMatrix.fn_shared_closure_0.body 2) =
      (true, false) := by
  rfl

/-- C11: direct targets are compatible and enter with unchanged arguments, even for closure bodies. -/
theorem direct_target_skips_closure_gate :
    (checkCalleeTargetCompatible { defPath := sharedPath, isIndirect := false } Mir.ClosureMatrix.fn_shared_closure_0.body 2, calleeEntryArgs { defPath := sharedPath, isIndirect := false } Mir.ClosureMatrix.fn_shared_closure_0.body [envScalar, u32v 5]) =
      (true, [envScalar, u32v 5]) := by
  rfl

/-- Indirect targets prepend `.scalar ⟨1, 8⟩` (`&`, `&mut`) or `.aggregate 0 []` (by value). -/
theorem indirect_target_prepends_env :
    (calleeEntryArgs { defPath := sharedPath, isIndirect := true } Mir.ClosureMatrix.fn_shared_closure_0.body [u32v 5], calleeEntryArgs { defPath := "closure_matrix::fn_once_kind::{closure#0}", isIndirect := true } Mir.ClosureMatrix.fn_once_kind_closure_0.body [u32v 5]) =
      ([.scalar ⟨1, 8⟩, u32v 5], [.aggregate 0 .nil, u32v 5]) := by
  rfl

/-- `ClosureFnPointer(Safe)` to `fn(u32) -> u32`. -/
theorem coerce_safe_ok :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ok := by
  rfl

/-- `ClosureFnPointer(Unsafe)` to `unsafe fn(u32) -> u32`. -/
theorem coerce_unsafe_ok :
    coerce "ClosureFnPointer(Unsafe)" sharedClo (.aggregate 0 .nil) ufnU32 [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ok := by
  rfl

/-- Safety mismatch: `ClosureFnPointer(Safe)` to an `unsafe fn` pointer. -/
theorem coerce_safe_to_unsafe_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) ufnU32 [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Safety mismatch: `ClosureFnPointer(Unsafe)` to a safe `fn` pointer. -/
theorem coerce_unsafe_to_safe_is_ub :
    coerce "ClosureFnPointer(Unsafe)" sharedClo (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- A capturing (`u32`) closure value never coerces. -/
theorem coerce_capturing_is_ub :
    coerce "ClosureFnPointer(Safe)" capClo (.aggregate 0 [u32v 7]) fnU32 [Mir.ClosureMatrix.capturing_direct_closure_0.body] =
      .ub := by
  rfl

/-- A capturing (`()`) closure value never coerces. -/
theorem coerce_zst_capturing_is_ub :
    coerce "ClosureFnPointer(Safe)" capZstClo (.aggregate 0 [.unit]) fnU32 [Mir.ClosureMatrix.capturing_direct_closure_1.body] =
      .ub := by
  rfl

/-- A capturing (`()`) closure type never coerces, even with an empty value. -/
theorem coerce_zst_capturing_empty_value_is_ub :
    coerce "ClosureFnPointer(Safe)" capZstClo (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.capturing_direct_closure_1.body] =
      .ub := by
  rfl

/-- Closures coerce only to Rust-ABI pointers. -/
theorem coerce_extern_c_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K] u32K .safe .c) [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Signature arity mismatch. -/
theorem coerce_arity_mismatch_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K, u32K] u32K .safe .rust) [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Parameter type mismatch. -/
theorem coerce_param_mismatch_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [.uint .u64] u32K .safe .rust) [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Return type mismatch. -/
theorem coerce_return_mismatch_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K] (.uint .u64) .safe .rust) [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- C5: a generic closure body is `.unsupported`, never `.ub`. -/
theorem coerce_generic_is_unsupported :
    coerce "ClosureFnPointer(Safe)" (.closure genericPath .nil) (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .unsupported := by
  rfl

/-- A capturing closure body linked under a non-capturing closure type is `.ub`. -/
theorem coerce_linked_capturing_body_is_ub :
    coerce "ClosureFnPointer(Safe)" (.closure capPath .nil) (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.capturing_direct_closure_0.body] =
      .ub := by
  rfl

/-- A non-closure body linked under the closure path is `.ub`. -/
theorem coerce_non_closure_body_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [{ Mir.ClosureMatrix.helper_triple.body with defPath := sharedPath }] =
      .ub := by
  rfl

/-- An unlinked closure body coerces (calls are then external). -/
theorem coerce_unlinked_ok :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [] =
      .ok := by
  rfl

/-- The pre-fix `args.types()` closure encoding never coerces. -/
theorem coerce_legacy_encoding_is_ub :
    coerce "ClosureFnPointer(Safe)" (.closure sharedPath [.int .i8, .fnPtr [.tuple [u32K]] u32K .safe (.other "rust-call"), .tuple .nil]) (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Function-item reification is unchanged. -/
theorem reify_fn_item_still_ok :
    coerce "ReifyFnPointer(Safe)" (.fnDef "closure_matrix::helper_triple" .nil) .unit fnU32 [Mir.ClosureMatrix.helper_triple.body] =
      .ok := by
  rfl

/-- `Fn` closure (`_1 : &{closure}`) reified with `ClosureFnPointer(Safe)` and called: `5 + 17`. -/
theorem fn_shared_is_22 :
    runWith Mir.ClosureMatrix.fn_shared.body [u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- `FnMut` closure (`_1 : &mut {closure}`), passed through the generic `id_mut` first. -/
theorem fn_mut_kind_is_7 :
    runWith Mir.ClosureMatrix.fn_mut_kind.body [u32v 5] [Mir.ClosureMatrix.id_mut.body, Mir.ClosureMatrix.fn_mut_kind_closure_0.body] =
      .normalScalar 7 4 := by
  rfl

/-- `FnOnce` closure (`_1 : {closure}` by value), passed through the generic `id_once` first. -/
theorem fn_once_kind_is_8 :
    runWith Mir.ClosureMatrix.fn_once_kind.body [u32v 5] [Mir.ClosureMatrix.id_once.body, Mir.ClosureMatrix.fn_once_kind_closure_0.body] =
      .normalScalar 8 4 := by
  rfl

/-- Zero-argument closure (`argCount = 1`, environment only). -/
theorem zero_arg_is_7 :
    runWith Mir.ClosureMatrix.zero_arg.body [] [Mir.ClosureMatrix.zero_arg_closure_0.body] =
      .normalScalar 7 4 := by
  rfl

/-- Two-argument closure: `6 ^ 3`. -/
theorem two_arg_is_5 :
    runWith Mir.ClosureMatrix.two_arg.body [u32v 6, u32v 3] [Mir.ClosureMatrix.two_arg_closure_0.body] =
      .normalScalar 5 4 := by
  rfl

/-- `ClosureFnPointer(Unsafe)` to an `unsafe fn` pointer, called in `unsafe`: `5 ^ 17`. -/
theorem unsafe_closure_is_20 :
    runWith Mir.ClosureMatrix.unsafe_closure.body [u32v 5] [Mir.ClosureMatrix.unsafe_closure_closure_0.body] =
      .normalScalar 20 4 := by
  rfl

/-- `UnsafeFnPointer` widening keeps the pointer: `FnPtrToPtr` of both pointers compare equal (`raw_c == raw_d`), `(5 + 1) ^ (1 << 8)`. -/
theorem widen_and_identity_is_262 :
    runWith Mir.ClosureMatrix.widen_and_identity.body [u32v 5] [Mir.ClosureMatrix.widen_and_identity_closure_0.body] =
      .normalScalar 262 4 := by
  rfl

/-- A function item and a closure reified side by side: `(4 * 3) ^ (4 * 5)`. -/
theorem mixed_fn_item_and_closure_is_24 :
    runWith Mir.ClosureMatrix.mixed_fn_item_and_closure.body [u32v 4] [Mir.ClosureMatrix.helper_triple.body, Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0.body] =
      .normalScalar 24 4 := by
  rfl

/-- `TerminatorKind.tailCall` (`become f(x)`) through a closure pointer: `9 ^ 5`. -/
theorem tail_call_is_12 :
    runWith Mir.ClosureMatrix.tail_through_closure.body [u32v 9] [Mir.ClosureMatrix.tail_through_closure_closure_0.body] =
      .normalScalar 12 4 := by
  rfl

/-- Diverging call (`target = none`) of a `fn(u32) -> !` closure pointer whose body panics. -/
theorem diverging_call_panics :
    runWith Mir.ClosureMatrix.diverging_closure.body [u32v 0] ([Mir.ClosureMatrix.diverging_closure_closure_0.body] ++ fmtStubs) =
      .panic := by
  rfl

/-- The same function when the diverging call is not reached. -/
theorem diverging_call_not_taken_is_3 :
    runWith Mir.ClosureMatrix.diverging_closure.body [u32v 3] ([Mir.ClosureMatrix.diverging_closure_closure_0.body] ++ fmtStubs) =
      .normalScalar 3 4 := by
  rfl

/-- `UnwindAction.cleanup`: the closure panics, the caller drops its guard in the cleanup block and resumes unwinding. -/
theorem unwind_cleanup_panics :
    runWith Mir.ClosureMatrix.unwind_through_closure.body [u32v 0] ([Mir.ClosureMatrix.unwind_through_closure_closure_0.body, Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .panic := by
  rfl

/-- The same call when the closure returns normally. -/
theorem unwind_cleanup_normal_is_4 :
    runWith Mir.ClosureMatrix.unwind_through_closure.body [u32v 4] ([Mir.ClosureMatrix.unwind_through_closure_closure_0.body, Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .normalScalar 4 4 := by
  rfl

/-- `UnwindAction.continue_` on the closure call: the panic propagates. -/
theorem unwind_continue_panics :
    runWith (setBb0CallUnwind Mir.ClosureMatrix.unwind_through_closure.body .continue_) [u32v 0] ([Mir.ClosureMatrix.unwind_through_closure_closure_0.body, Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .panic := by
  rfl

/-- `UnwindAction.terminate` on the closure call: unwinding aborts. -/
theorem unwind_terminate_aborts :
    runWith (setBb0CallUnwind Mir.ClosureMatrix.unwind_through_closure.body .terminate) [u32v 0] ([Mir.ClosureMatrix.unwind_through_closure_closure_0.body, Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .abort := by
  rfl

/-- `UnwindAction.unreachable` on the closure call: unwinding is undefined behavior. -/
theorem unwind_unreachable_is_ub :
    runWith (setBb0CallUnwind Mir.ClosureMatrix.unwind_through_closure.body .unreachable) [u32v 0] ([Mir.ClosureMatrix.unwind_through_closure_closure_0.body, Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .ub := by
  rfl

/-- `const_eval_select` with a closure pointer as runtime target, as captured (rustc lowers it to an indirect call): `4 + 17`. -/
theorem const_eval_select_lowered_is_21 :
    runWith Mir.ClosureMatrix.ces_through_closure_fn_ptr.body [u32v 4] [Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0.body] =
      .normalScalar 21 4 := by
  rfl

/-- C5: a closure inside a generic function: the closure type carries no parent generic arguments, so the coercion is `.unsupported` (never `.ub`). -/
theorem generic_closure_is_unsupported :
    runWith Mir.ClosureMatrix.call_generic.body [u32v 77] [Mir.ClosureMatrix.generic_closure.body, Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .unsupported := by
  rfl

/-- C11: a direct closure call goes through `<{closure} as Fn<(u32,)>>::call` (`isIndirect = false`) and stays an external call (no false `.ub`). -/
theorem direct_fn_trait_call_is_external :
    runWith Mir.ClosureMatrix.direct_closure_call.body [u32v 1] [Mir.ClosureMatrix.direct_closure_call_closure_0.body] =
      .ext "core::ops::Fn::call" := by
  rfl

/-- Without the closure body the coercion succeeds and the call is external (never `.ub`). -/
theorem unlinked_closure_is_external :
    runWith Mir.ClosureMatrix.fn_shared.body [u32v 5] [] =
      .ext "closure_matrix::fn_shared::{closure#0}" := by
  rfl

/-- Callee-directed dispatch: a pointer to the closure that never went through a coercion in this run is entered with the synthesized environment. -/
theorem untagged_closure_pointer_dispatches :
    runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath fnU32] =
      .normalScalar 22 4 := by
  rfl

/-- C10: a forged `(N + 1)`-argument pointer `fn(&{closure}, u32) -> u32` to a non-capturing closure body is `.ub`. -/
theorem forged_env_call_non_capturing_is_ub :
    runWith (envPtrCaller (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust) (.ref .not sharedClo)) [fnPtrVal, envScalar, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10: a forged `(N + 1)`-argument pointer to a capturing (`u32`) closure body is `.ub`. -/
theorem forged_env_call_capturing_is_ub :
    runWith (envPtrCaller (.fnPtr [.ref .not capClo, u32K] u32K .safe .rust) (.ref .not capClo)) [fnPtrVal, envScalar, u32v 5] [Mir.ClosureMatrix.capturing_direct_closure_0.body] [entry capPath (.fnPtr [.ref .not capClo, u32K] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10: a forged `(N + 1)`-argument pointer to a capturing (`()`) closure body is `.ub`. -/
theorem forged_env_call_zst_capturing_is_ub :
    runWith (envPtrCaller (.fnPtr [.ref .not capZstClo, u32K] u32K .safe .rust) (.ref .not capZstClo)) [fnPtrVal, envScalar, u32v 5] [Mir.ClosureMatrix.capturing_direct_closure_1.body] [entry capZstPath (.fnPtr [.ref .not capZstClo, u32K] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10: an `N`-argument pointer to a capturing closure body is `.ub` (no environment can be synthesized). -/
theorem pointer_to_capturing_closure_is_ub :
    runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.capturing_direct_closure_0.body] [entry capPath fnU32] =
      .ub := by
  rfl

/-- A pointer to the closure transmuted to `fn(u64) -> u32` is `.ub`. -/
theorem transmuted_signature_is_ub :
    runWith (ptrCaller (.fnPtr [.uint .u64] u32K .safe .rust) (.uint .u64)) [fnPtrVal, .scalar ⟨5, 8⟩] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [.uint .u64] u32K .safe .rust)] =
      .ub := by
  rfl

/-- A pointer to the closure with the `extern "C"` ABI is `.ub`. -/
theorem extern_c_pointer_is_ub :
    runWith (ptrCaller (.fnPtr [u32K] u32K .safe .c)) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [u32K] u32K .safe .c)] =
      .ub := by
  rfl

/-- C11: a direct (`isIndirect = false`) call of the linked closure body passing its environment explicitly is entered unchanged. -/
theorem direct_env_call_succeeds :
    runWith (directEnvCaller sharedPath (.ref .not sharedClo)) [envScalar, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- A forged non-capturing closure body that reads `(*_1).0` faults: the synthesized environment has no provenance. -/
theorem forged_env_read_is_ub :
    runWith Mir.ClosureMatrix.fn_shared.body [u32v 5] [forgedEnvReadBody] =
      .ub := by
  rfl

/-- Contrast: the same forged body reading its argument `_2` returns normally, so the fault above comes from the environment read. -/
theorem forged_arg_read_contrast_is_5 :
    runWith Mir.ClosureMatrix.fn_shared.body [u32v 5] [forgedArgReadBody] =
      .normalScalar 5 4 := by
  rfl

/-- Inline `const_eval_select` with a closure pointer as runtime target: dispatched with the synthesized environment. -/
theorem inline_ces_indirect_closure_is_22 :
    runWith (cesCaller fnU32) [u32v 5, fnPtrVal] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath fnU32] =
      .normalScalar 22 4 := by
  rfl

/-- Inline `const_eval_select` with a non-capturing closure value as runtime target. -/
theorem inline_ces_direct_closure_is_22 :
    runWith (cesCaller sharedClo) [u32v 5, .aggregate 0 .nil] [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- Inline `const_eval_select` with a capturing closure value as runtime target is `.unsupported` (never `.ub`). -/
theorem inline_ces_direct_capturing_is_unsupported :
    runWith (cesCaller capClo) [u32v 5, .aggregate 0 [u32v 7]] [Mir.ClosureMatrix.capturing_direct_closure_0.body] =
      .unsupported := by
  rfl

/-- C5: inline `const_eval_select` with a generic closure body as runtime target is `.unsupported` (never `.ub`). -/
theorem inline_ces_generic_closure_is_unsupported :
    runWith (cesCaller (.closure genericPath .nil)) [u32v 5, .aggregate 0 .nil] [Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .unsupported := by
  rfl

/-- C10: inline `const_eval_select` through a pointer to a capturing closure body is `.ub`. -/
theorem inline_ces_indirect_capturing_is_ub :
    runWith (cesCaller fnU32) [u32v 5, fnPtrVal] [Mir.ClosureMatrix.capturing_direct_closure_0.body] [entry capPath fnU32] =
      .ub := by
  rfl

/-- Inline `const_eval_select` through an `extern "C"` pointer to the closure is `.ub`. -/
theorem inline_ces_extern_c_is_ub :
    runWith (cesCaller (.fnPtr [u32K] u32K .safe .c)) [u32v 5, fnPtrVal] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [u32K] u32K .safe .c)] =
      .ub := by
  rfl

/-- `fn(_1 : sigKind, _2 : u32) -> ! { _0 = _1(_2) }` (diverging indirect call). -/
def divPtrCaller (sigKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::div_ptr_caller"
    argCount := 2
    localDecls := [decl .never 2, decl sigKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .call (.copy (plc 1)) [.copy (plc 2)] (plc 0) .none .continue_
             span := "div_ptr_call" }
         isCleanup := false }] }

/-- `fn(_1 : sigKind, _2 : u32) -> u32 { become _1(_2) }` (indirect tail call). -/
def tailPtrCaller (sigKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::tail_ptr_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl sigKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .tailCall (.copy (plc 1)) [.copy (plc 2)]
             span := "tail_ptr_call" }
         isCleanup := false }] }

/-- `fn(_1 : sigKind, _2 : envKind, _3 : u32) -> u32 { become _1(_2, _3) }`: forged `(N + 1)`-arg indirect tail call. -/
def tailEnvPtrCaller (sigKind envKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::tail_env_ptr_caller"
    argCount := 3
    localDecls := [decl u32K 0, decl sigKind 1, decl envKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .tailCall (.copy (plc 1)) [.copy (plc 2), .copy (plc 3)]
             span := "tail_env_ptr_call" }
         isCleanup := false }] }

/-- Inline `const_eval_select` carrying `rtKind` solely on the operand local `_2` (`target.typeArgs = []`). -/
def cesOperandTyOnlyCaller (rtKind : RigidTy) : CapturedMir :=
  { Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::ces_op_ty_only_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl u32K 0, decl rtKind 1, decl (.tuple [u32K]) 0]
    basicBlocks :=
      [{ statements :=
           [{ kind := .storageLive 3, span := "ces_live" },
            { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
         terminator :=
           { kind :=
               .call
                 (.constant
                   { ty := { kind := .fnDef "core::intrinsics::const_eval_select" .nil
                             layoutIdx := 2 }
                     val := .zeroSized })
                 [.move (plc 3),
                  .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                              val := .zeroSized },
                  .copy (plc 2)]
                 (plc 0) (.some 1) .continue_
             span := "ces_call" }
         isCleanup := false },
       retBlock] }

/-- C5: indirect normal call, diverging call, tail call, and indirect `const_eval_select` to a linked generic closure body all report `.unsupported` (never `.ub` or `.ext`). -/
theorem indirect_generic_closure_all_sites_unsupported :
    (runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath fnU32],
     runWith (divPtrCaller (.fnPtr [u32K] .never .safe .rust)) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath (.fnPtr [u32K] .never .safe .rust)],
     runWith (tailPtrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath fnU32],
     runWith (cesCaller fnU32) [u32v 5, fnPtrVal] [Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath fnU32]) =
      (.unsupported, .unsupported, .unsupported, .unsupported) := by
  rfl

/-- Direct `const_eval_select` resolves a non-capturing closure type carried on `operandTy` even when `target.typeArgs` is empty. -/
theorem inline_ces_direct_closure_from_operand_ty_only_is_22 :
    runWith (cesOperandTyOnlyCaller sharedClo) [u32v 5, .aggregate 0 .nil] [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- Forged scalar runtime target for a generic closure type in `const_eval_select` faults with `.ub` (never `.unsupported`). -/
theorem inline_ces_forged_scalar_generic_closure_is_ub :
    runWith (cesCaller (.closure genericPath .nil)) [u32v 5, u32v 99] [Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .ub := by
  rfl

/-- Direct `const_eval_select` rejects a non-Rust ABI closure body with `.ub`. -/
theorem inline_ces_direct_non_rust_abi_closure_is_ub :
    let cAbiClosure :=
      { Mir.ClosureMatrix.fn_shared_closure_0.body with
        fnAbi := { Mir.ClosureMatrix.fn_shared_closure_0.body.fnAbi with conv := .c } }
    runWith (cesCaller sharedClo) [u32v 5, .aggregate 0 .nil] [cAbiClosure] =
      .ub := by
  rfl

/-- Inline `const_eval_select` rejects a transmuted `fn(u64) -> u32` pointer to a closure with `.ub`. -/
theorem inline_ces_transmuted_signature_is_ub :
    let caller :=
      { Mir.ClosureMatrix.fn_shared.body with
        defPath := "tests::ces_transmute_caller"
        argCount := 2
        localDecls := [decl u32K 0, decl (.uint .u64) 1, decl (.fnPtr [.uint .u64] u32K .safe .rust) 1, decl (.tuple [.uint .u64]) 1]
        basicBlocks :=
          [{ statements :=
               [{ kind := .storageLive 3, span := "ces_live" },
                { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
             terminator :=
               { kind :=
                   .call
                     (.constant
                       { ty := { kind := .fnDef "core::intrinsics::const_eval_select"
                                   [.tuple [.uint .u64], .fnDef "closure_matrix::ct_add" .nil, .fnPtr [.uint .u64] u32K .safe .rust, u32K]
                                 layoutIdx := 2 }
                         val := .zeroSized })
                     [.move (plc 3),
                      .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                                  val := .zeroSized },
                      .copy (plc 2)]
                     (plc 0) (.some 1) .continue_
                 span := "ces_call" }
             isCleanup := false },
           retBlock] }
    runWith caller [.scalar ⟨5, 8⟩, fnPtrVal] [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [.uint .u64] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10 on `tailCall`: forged `(N + 1)`-arg tail call to non-capturing closure and tail call to capturing closure both fault with `.ub`. -/
theorem tail_call_forged_env_and_capturing_is_ub :
    (runWith (tailEnvPtrCaller (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust) (.ref .not sharedClo))
       [fnPtrVal, envScalar, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body]
       [entry sharedPath (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust)],
     runWith (tailPtrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.capturing_direct_closure_0.body]
       [entry capPath fnU32]) =
      (.ub, .ub) := by
  rfl

/-- `tailCall` through a closure pointer preserves frame-deallocation protector-conflict `.ub`. -/
theorem tail_call_protector_conflict_is_ub :
    let caller := tailPtrCaller fnU32
    let st : MirExecState :=
      .running
        { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocalsAux 0 caller.localDecls [fnPtrVal, u32v 5] }
          memory :=
            { memWith caller [Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath fnU32] with
              borrows :=
                [{ tag := 1
                   targetLocal := 2
                   targetProjection := .nil
                   perm := .unique
                   rangeOffset := 0
                   rangeLen := 4
                   protector := .some 1
                   parentTag := .none
                   targetFrameDepth := 0
                   allocDead := false }]
              activeProtectors := [1]
              nextTag := 2
              nextProtector := 2 } }
    run 400 caller st = .ub := by
  rfl

/-- Unlinked closure coercion still rejects non-Rust target ABI (`extern "C"`) with `.ub`. -/
theorem coerce_unlinked_extern_c_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K] u32K .safe .c) [] =
      .ub := by
  rfl


/-- Real-captured 2-level nested closure-to-`fn`-pointer call: `((10 ^ 3) ^ 7) + 1 = 15` (matches Miri). -/
theorem nested_fnptr_is_15 :
    runWith Mir.ClosureExtended.nested_fnptr.body [u32v 10]
      [Mir.ClosureExtended.nested_fnptr_closure_0.body,
       Mir.ClosureExtended.nested_fnptr_closure_0_closure_0.body] =
      .normalScalar 15 4 := by
  rfl

/-- Real-captured concrete trait-impl closure-to-`fn`-pointer call: `(10 + 5) ^ 19 = 28` (matches Miri). -/
theorem concrete_trait_impl_closure_is_28 :
    runWith Mir.ClosureExtended.call_concrete_trait_impl.body [u32v 10]
      [Mir.ClosureExtended.BoxedVal_as_Compute_compute.body,
       Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0.body] =
      .normalScalar 28 4 := by
  rfl

/-- C5 on real-captured default trait method: its closure inherits `Self` (`typeParamCount = 1`), so reification fails closed `.unsupported` (never `.ub`). -/
theorem default_trait_method_closure_is_unsupported :
    runWith Mir.ClosureExtended.call_default_trait_closure.body [u32v 10]
      [Mir.ClosureExtended.BoxedVal_as_Compute_compute.body,
       Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0.body,
       Mir.ClosureExtended.Compute_compute_default.body,
       Mir.ClosureExtended.Compute_compute_default_closure_0.body] =
      .unsupported := by
  rfl

/-- Real-captured `ClosureFnPointer` -> `FnPtrToPtr` -> `Transmute` -> indirect call roundtrip: `10 ^ 31 = 21` (matches Miri). -/
theorem fn_ptr_transmute_roundtrip_is_21 :
    runWith Mir.ClosureExtended.fn_ptr_transmute_roundtrip.body [u32v 10]
      [Mir.ClosureExtended.fn_ptr_transmute_roundtrip_closure_0.body] =
      .normalScalar 21 4 := by
  rfl

/-- Tree Borrows compatibility: a non-capturing closure body beginning with `Retag(FnEntry, _1)` succeeds when entered with the synthesized ZST reference `.scalar ⟨1, 8⟩`. -/
theorem closure_body_fn_entry_retag_succeeds :
    let base := Mir.ClosureMatrix.fn_shared_closure_0.body
    let retagBody :=
      { base with
        basicBlocks :=
          match base.basicBlocks with
          | bb0 :: rest =>
            { bb0 with
              statements :=
                { kind := .retag .fnEntry (plc 1), span := "retag_env" } :: bb0.statements } :: rest
          | .nil => .nil }
    runWith Mir.ClosureMatrix.fn_shared.body [u32v 5] [retagBody] =
      .normalScalar 22 4 := by
  rfl

/-- Forged `ClosureFnPointer(Safe)` targeting a generic non-closure `fn` item faults with `.ub` (never `.unsupported`). -/
theorem coerce_generic_non_closure_is_ub :
    let genFn : CapturedMir :=
      { Mir.ClosureMatrix.ct_add.body with
        defPath := "tests::gen_fn"
        typeParamCount := 1 }
    coerce "ClosureFnPointer(Safe)" (.closure "tests::gen_fn" .nil) (.aggregate 0 .nil) fnU32 [genFn] =
      .ub := by
  rfl

/-- C5 precedence on a forged linked body that is both capturing and generic (`typeParamCount = 1`): reification and an indirect call through a pointer to it fail closed with `.unsupported`, while the same capturing body without type parameters is `.ub` at both sites. -/
theorem generic_capturing_body_is_unsupported_not_ub :
    let genCap : CapturedMir :=
      { Mir.ClosureMatrix.capturing_direct_closure_0.body with typeParamCount := 1 }
    (coerce "ClosureFnPointer(Safe)" (.closure capPath .nil) (.aggregate 0 .nil) fnU32 [genCap],
     coerce "ClosureFnPointer(Safe)" (.closure capPath .nil) (.aggregate 0 .nil) fnU32
       [Mir.ClosureMatrix.capturing_direct_closure_0.body],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [genCap] [entry capPath fnU32],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.capturing_direct_closure_0.body]
       [entry capPath fnU32]) =
      (.unsupported, .ub, .unsupported, .ub) := by
  rfl

/-- Inline `const_eval_select` rejects a forged `.unit` value in a `fn`-pointer local even when `target.typeArgs[2]` names a valid closure. -/
theorem inline_ces_forged_unit_with_fnptr_operand_ty_is_ub :
    let caller :=
      { Mir.ClosureMatrix.fn_shared.body with
        defPath := "tests::ces_forged_unit_fnptr_ty"
        argCount := 2
        localDecls := [decl u32K 0, decl u32K 0, decl fnU32 1, decl (.tuple [u32K]) 0]
        basicBlocks :=
          [{ statements :=
               [{ kind := .storageLive 3, span := "ces_live" },
                { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
             terminator :=
               { kind :=
                   .call
                     (.constant
                       { ty := { kind := .fnDef "core::intrinsics::const_eval_select" (cesTyArgs sharedClo)
                                 layoutIdx := 2 }
                         val := .zeroSized })
                     [.move (plc 3),
                      .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                                  val := .zeroSized },
                      .copy (plc 2)]
                     (plc 0) (.some 1) .continue_
                 span := "ces_call" }
             isCleanup := false },
           retBlock] }
    runWith caller [u32v 5, .unit] [Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- `unpackConstEvalSelectArgs?` accepts a zero-sized tuple containing a non-capturing closure and rejects a capturing closure. -/
theorem unpack_ces_zst_closure_tuple :
    (unpackConstEvalSelectArgs? .unit (.some (.tuple [.closure "tests::c" .nil])),
     unpackConstEvalSelectArgs? .unit (.some (.tuple [.closure "tests::c" [u32K]]))) =
      (.some [.unit], .none) := by
  rfl

/-- Coercion-tag/callee-kind mismatches all fault with `.ub`: `ReifyFnPointer(Safe)` on a closure type, `ClosureFnPointer(Safe)` on a `fnDef` type, and forged `ReifyFnPointer(Safe)` on a `fnDef` naming a linked closure body even with an `(N + 1)`-arg signature. -/
theorem coerce_wrong_coercion_kind_is_ub :
    (coerce "ReifyFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [Mir.ClosureMatrix.fn_shared_closure_0.body],
     coerce "ClosureFnPointer(Safe)" (.fnDef "closure_matrix::ct_add" .nil) .unit fnU32 [Mir.ClosureMatrix.ct_add.body],
     coerce "ReifyFnPointer(Safe)" (.fnDef sharedPath .nil) .unit
       (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust)
       [Mir.ClosureMatrix.fn_shared_closure_0.body]) =
      (.ub, .ub, .ub) := by
  rfl

/-- Inline `const_eval_select` rejects a forged `.closure` runtime target naming a linked non-closure `fn` item with `.ub` (never executing it and never returning `.unsupported` when generic). -/
theorem inline_ces_forged_closure_ty_on_non_closure_is_ub :
    let genFn : CapturedMir :=
      { Mir.ClosureMatrix.ct_add.body with
        defPath := "tests::gen_fn"
        typeParamCount := 1 }
    (runWith (cesCaller (.closure "closure_matrix::ct_add" .nil)) [u32v 5, .aggregate 0 .nil]
       [Mir.ClosureMatrix.ct_add.body],
     runWith (cesCaller (.closure "tests::gen_fn" .nil)) [u32v 5, .aggregate 0 .nil]
       [genFn]) =
      (.ub, .ub) := by
  rfl

/-- C5 precedence on inline `const_eval_select` with a linked generic capturing closure body (`typeParamCount = 1`): `.unsupported`, while the non-generic capturing body with forged `.closure capPath .nil` faults with `.ub`. -/
theorem inline_ces_generic_capturing_is_unsupported_not_ub :
    let genCap : CapturedMir :=
      { Mir.ClosureMatrix.capturing_direct_closure_0.body with typeParamCount := 1 }
    (runWith (cesCaller (.closure capPath .nil)) [u32v 5, .aggregate 0 .nil] [genCap],
     runWith (cesCaller (.closure capPath .nil)) [u32v 5, .aggregate 0 .nil]
       [Mir.ClosureMatrix.capturing_direct_closure_0.body]) =
      (.unsupported, .ub) := by
  rfl

/-- Untyped `FnPtrEntry` (`fnSig = .none`) targeting a closure body: `N`-arg Rust-ABI call dispatches (`22`), while forged `(N + 1)`-arg call, capturing body, and non-Rust ABI body all fault with `.ub` (C10 without `fnSig`). -/
theorem untyped_fnptr_entry_closure_dispatch_and_c10 :
    let untypedEntry (p : DefPath) : FnPtrEntry :=
      { allocId := 65536, defPath := p, typeArgs := .nil, fnSig := .none }
    let cAbiClosure :=
      { Mir.ClosureMatrix.fn_shared_closure_0.body with
        fnAbi := { Mir.ClosureMatrix.fn_shared_closure_0.body.fnAbi with conv := .c } }
    (runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body]
       [untypedEntry sharedPath],
     runWith (envPtrCaller (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust) (.ref .not sharedClo))
       [fnPtrVal, envScalar, u32v 5] [Mir.ClosureMatrix.fn_shared_closure_0.body]
       [untypedEntry sharedPath],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [Mir.ClosureMatrix.capturing_direct_closure_0.body]
       [untypedEntry capPath],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [cAbiClosure]
       [untypedEntry sharedPath]) =
      (.normalScalar 22 4, .ub, .ub, .ub) := by
  rfl

end Anneal.ClosureFnPtrTests.V06

/-! ## 6. Closure function-pointer matrix on `V2026_08_01` -/

namespace Anneal.ClosureFnPtrTests.V08Strict

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! Test-local copy of the `Anneal.Rustc.V2026_06_01.Lower` spine-normalizing
`stepMirState` wrappers, re-targeted at `V2026_08_01` (each wrapper is proved equal to
the trusted function it normalizes). -/

@[reducible]
def strictBool : Bool → Option Bool
  | false => .some false
  | true => .some true

theorem strictBool_eq : ∀ (b : Bool), strictBool b = .some b
  | false => rfl
  | true => rfl

/--
Binary spine normalizer for `Nat` (`k` halving rounds via `Nat.div` / `Nat.mod`).
Kernel and `Meta.whnf` only reduce `Nat.div` / `Nat.mod` when their argument is
closed, so callers should go through `strictBits`, which first peels a few
successor layers structurally.
-/
@[reducible]
def strictBitsCore : Nat → Nat → Option Nat
  | .zero, n => .some n
  | .succ _, .zero => .some .zero
  | .succ _, .succ .zero => .some (.succ .zero)
  | .succ k, .succ (.succ m) =>
    let n := .succ (.succ m)
    match strictBitsCore k (Nat.div n 2), Nat.beq (Nat.mod n 2) 0 with
    | .some q, true => .some (Nat.mul 2 q)
    | .some q, false => .some (.succ (Nat.mul 2 q))
    | .none, _ => .none

theorem strictBitsCore_eq : ∀ (k n : Nat), strictBitsCore k n = .some n
  | .zero, _ => rfl
  | .succ _, .zero => rfl
  | .succ _, .succ .zero => rfl
  | .succ k, .succ (.succ m) => by
    unfold strictBitsCore
    dsimp only
    rw [strictBitsCore_eq k (Nat.div (.succ (.succ m)) 2)]
    cases hm : Nat.beq (Nat.mod (.succ (.succ m)) 2) 0
    · dsimp only
      have hm' : (.succ (.succ m)) % 2 ≠ 0 := fun hc => by
        change Nat.mod (.succ (.succ m)) 2 = 0 at hc
        rw [hc] at hm
        nomatch hm
      change Option.some (2 * ((m + 2) / 2) + 1) = Option.some (m + 2)
      exact congrArg Option.some (by omega)
    · dsimp only
      have hm' : (.succ (.succ m)) % 2 = 0 := Nat.eq_of_beq_eq_true hm
      change Option.some (2 * ((m + 2) / 2)) = Option.some (m + 2)
      exact congrArg Option.some (by omega)

/--
Spine-normalize a `Nat` to a canonical literal, with `k` binary halving rounds.

Open-term robustness: periodic closed-term stepping (`stepMirStatePeriodic`)
leaves up to two raw `stepMirState` increments between normalizations, so
counters such as `StackFrame.stmtIdx`, `Memory.nextTag`, or
`BorrowEntry.targetFrameDepth` arrive here as `Nat.succ (Nat.add (s.frame.stmtIdx) 0)`
thunks whose *syntax* still mentions the previous state `s`. When `s` contains a
free variable (an unused symbolic caller parameter `x`), `Meta.whnf` refuses to
evaluate `Nat.div` / `Nat.mod` on such terms (`hasFVar`), stalling `by rfl`.
Matching `k` first preserves `strictBits 0 x = .some x` definitionally on open
`x`, and for `k = .succ _` `strictBits` peels up to eight `Nat.succ` layers
structurally (covering up to seven stacked increments over an fvar-bearing
state projection and rebinding the closed sub-numeral) before handing the
closed remainder to `strictBitsCore`.
-/
@[reducible]
def strictBits : Nat → Nat → Option Nat
  | .zero, n => .some n
  | .succ k, n =>
    match n with
    | .zero => .some .zero
    | .succ .zero => .some 1
    | .succ (.succ .zero) => .some 2
    | .succ (.succ (.succ .zero)) => .some 3
    | .succ (.succ (.succ (.succ .zero))) => .some 4
    | .succ (.succ (.succ (.succ (.succ .zero)))) => .some 5
    | .succ (.succ (.succ (.succ (.succ (.succ .zero))))) => .some 6
    | .succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))) => .some 7
    | .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ m))))))) =>
      strictBitsCore (.succ k) (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ m))))))))

theorem strictBits_eq : ∀ (k n : Nat), strictBits k n = .some n
  | .zero, _ => rfl
  | .succ k, n => by
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
    all_goals first
      | rfl
      | exact strictBitsCore_eq (.succ k) _

@[reducible]
def strictOpt {α : Type} : Option α → Option (Option α)
  | .none => .some .none
  | .some x => .some (.some x)

theorem strictOpt_eq {α : Type} : ∀ (o : Option α), strictOpt o = .some o
  | .none => rfl
  | .some _ => rfl

@[reducible]
def strictOptNat : Option Nat → Option (Option Nat)
  | .none => .some .none
  | .some n =>
    match strictBits 32 n with
    | .some n' => .some (.some n')
    | .none => .none

theorem strictOptNat_eq : ∀ (o : Option Nat), strictOptNat o = .some o
  | .none => rfl
  | .some n => by
    unfold strictOptNat
    dsimp only
    rw [strictBits_eq 32 n]

@[reducible]
def strictList {α : Type} : List α → Option (List α)
  | .nil => .some .nil
  | x :: xs =>
    match strictList xs with
    | .some xs' => .some (x :: xs')
    | .none => .none

theorem strictList_eq {α : Type} : ∀ (xs : List α), strictList xs = .some xs
  | .nil => rfl
  | _ :: xs => by
    unfold strictList
    rw [strictList_eq xs]

@[reducible]
def mapStrictList {α : Type} (f : α → Option α) : List α → Option (List α)
  | .nil => .some .nil
  | x :: xs =>
    match f x, mapStrictList f xs with
    | .some x', .some xs' => .some (x' :: xs')
    | _, _ => .none

theorem mapStrictList_eq {α : Type} (f : α → Option α) (hf : ∀ x, f x = .some x) :
    ∀ (xs : List α), mapStrictList f xs = .some xs
  | .nil => rfl
  | x :: xs => by
    unfold mapStrictList
    rw [hf x, mapStrictList_eq f hf xs]

@[reducible]
def strictPerm : TreeBorrowPerm → Option TreeBorrowPerm
  | .cell => .some .cell
  | .reservedFrz b =>
    match strictBool b with
    | .some b' => .some (.reservedFrz b')
    | .none => .none
  | .reservedIM => .some .reservedIM
  | .unique => .some .unique
  | .frozen => .some .frozen
  | .disabled => .some .disabled

theorem strictPerm_eq : ∀ (p : TreeBorrowPerm), strictPerm p = .some p
  | .cell => rfl
  | .reservedFrz b => by
    unfold strictPerm
    dsimp only
    rw [strictBool_eq b]
  | .reservedIM => rfl
  | .unique => rfl
  | .frozen => rfl
  | .disabled => rfl

/--
Spine-normalize a `ProjectionElem`: collapse `Nat` field/local/variant indices
(`strictBits 16`), constant-index / subslice offsets and lengths (`strictBits 64`),
and `fromEnd` flags (`strictBool`) to canonical literals, while leaving static
`Ty` and `Option String` payloads untouched. Collapses runtime
`.constantIndex sc.bits 0 false` and `normalizeSubsliceProjections` `Nat.add` /
`Nat.sub` thunks before they are copied into `BorrowEntry.targetProjection`,
`SavedCallerFrame.destination`, or subsequent `Place`s.
-/
@[reducible]
def strictProjectionElem : ProjectionElem → Option ProjectionElem
  | .deref => .some .deref
  | .field f ty =>
    match strictBits 16 f with
    | .some f' => .some (.field f' ty)
    | .none => .none
  | .index i =>
    match strictBits 16 i with
    | .some i' => .some (.index i')
    | .none => .none
  | .constantIndex off minLen fromEnd =>
    match strictBits 64 off, strictBits 64 minLen, strictBool fromEnd with
    | .some off', .some minLen', .some fromEnd' => .some (.constantIndex off' minLen' fromEnd')
    | _, _, _ => .none
  | .subslice fromIdx toIdx fromEnd =>
    match strictBits 64 fromIdx, strictBits 64 toIdx, strictBool fromEnd with
    | .some fromIdx', .some toIdx', .some fromEnd' => .some (.subslice fromIdx' toIdx' fromEnd')
    | _, _, _ => .none
  | .downcast name v =>
    match strictBits 16 v with
    | .some v' => .some (.downcast name v')
    | .none => .none
  | .opaqueCast ty => .some (.opaqueCast ty)
  | .unwrapUnsafeBinder ty => .some (.unwrapUnsafeBinder ty)

theorem strictProjectionElem_eq : ∀ (pe : ProjectionElem), strictProjectionElem pe = .some pe
  | .deref => rfl
  | .field f ty => by
    unfold strictProjectionElem
    dsimp only
    rw [strictBits_eq 16 f]
  | .index i => by
    unfold strictProjectionElem
    dsimp only
    rw [strictBits_eq 16 i]
  | .constantIndex off minLen fromEnd => by
    unfold strictProjectionElem
    dsimp only
    rw [strictBits_eq 64 off, strictBits_eq 64 minLen, strictBool_eq fromEnd]
  | .subslice fromIdx toIdx fromEnd => by
    unfold strictProjectionElem
    dsimp only
    rw [strictBits_eq 64 fromIdx, strictBits_eq 64 toIdx, strictBool_eq fromEnd]
  | .downcast name v => by
    unfold strictProjectionElem
    dsimp only
    rw [strictBits_eq 16 v]
  | .opaqueCast _ => rfl
  | .unwrapUnsafeBinder _ => rfl

/-- Spine-normalize a `Place`: root local (`strictBits 16`) and every projection
element (`mapStrictList strictProjectionElem`). -/
@[reducible]
def strictPlace (p : Place) : Option Place :=
  match strictBits 16 p.local_, mapStrictList strictProjectionElem p.projection with
  | .some loc', .some proj' => .some { local_ := loc', projection := proj' }
  | _, _ => .none

theorem strictPlace_eq (p : Place) : strictPlace p = .some p := by
  cases p
  unfold strictPlace
  dsimp only
  rw [strictBits_eq, mapStrictList_eq strictProjectionElem strictProjectionElem_eq]

/-- Spine-normalize an `UnwindAction` (collapsing `narrowCallStackForTailCallee`
head-update thunks and `.cleanup` block-index arithmetic). -/
@[reducible]
def strictUnwindAction : UnwindAction → Option UnwindAction
  | .cleanup bb =>
    match strictBits 16 bb with
    | .some bb' => .some (.cleanup bb')
    | .none => .none
  | .unreachable => .some .unreachable
  | .terminate => .some .terminate
  | .continue_ => .some .continue_

theorem strictUnwindAction_eq : ∀ (u : UnwindAction), strictUnwindAction u = .some u
  | .cleanup bb => by
    unfold strictUnwindAction
    dsimp only
    rw [strictBits_eq 16 bb]
  | .unreachable => rfl
  | .terminate => rfl
  | .continue_ => rfl

@[reducible]
def strictBorrowEntry (e : BorrowEntry) : Option BorrowEntry :=
  match strictBits 32 e.tag, strictBits 16 e.targetLocal,
      mapStrictList strictProjectionElem e.targetProjection, strictPerm e.perm with
  | .some tag', .some loc', .some proj', .some perm' =>
    match strictBits 64 e.rangeOffset, strictBits 64 e.rangeLen, strictOptNat e.protector with
    | .some roff', .some rlen', .some prot' =>
      match strictOptNat e.parentTag, strictBits 16 e.targetFrameDepth, strictBool e.allocDead with
      | .some ptag', .some depth', .some dead' =>
        .some
          { tag := tag'
            targetLocal := loc'
            targetProjection := proj'
            perm := perm'
            rangeOffset := roff'
            rangeLen := rlen'
            protector := prot'
            parentTag := ptag'
            targetFrameDepth := depth'
            allocDead := dead' }
      | _, _, _ => .none
    | _, _, _ => .none
  | _, _, _, _ => .none

theorem strictBorrowEntry_eq (e : BorrowEntry) : strictBorrowEntry e = .some e := by
  cases e
  unfold strictBorrowEntry
  dsimp only
  rw [strictBits_eq, strictBits_eq,
      mapStrictList_eq strictProjectionElem strictProjectionElem_eq, strictPerm_eq,
      strictBits_eq, strictBits_eq, strictOptNat_eq, strictOptNat_eq,
      strictBits_eq, strictBool_eq]

@[reducible]
def strictBorrows : List BorrowEntry → Option (List BorrowEntry)
  | .nil => .some .nil
  | e :: rest =>
    match strictBorrowEntry e, strictBorrows rest with
    | .some e', .some rest' => .some (e' :: rest')
    | _, _ => .none

theorem strictBorrows_eq : ∀ (bs : List BorrowEntry), strictBorrows bs = .some bs
  | .nil => rfl
  | e :: rest => by
    unfold strictBorrows
    rw [strictBorrowEntry_eq e, strictBorrows_eq rest]

@[reducible]
def strictValue : Nat → Value → Option Value
  | .zero, v => .some v
  | .succ _, .unit => .some .unit
  | .succ _, .scalar sc =>
    match strictBits 128 sc.bits, strictBits 16 sc.sizeBytes with
    | .some b', .some sz' => .some (.scalar ⟨b', sz'⟩)
    | _, _ => .none
  | .succ _, .ptr p sz =>
    match strictBits 64 p.allocId, strictBits 64 p.offsetBytes, strictBits 16 sz with
    | .some a', .some o', .some sz' => .some (.ptr ⟨a', o'⟩ sz')
    | _, _, _ => .none
  | .succ d, .aggregate v fs =>
    match strictBits 16 v, mapStrictList (strictValue d) fs with
    | .some v', .some fs' => .some (.aggregate v' fs')
    | _, _ => .none

theorem strictValue_eq : ∀ (d : Nat) (v : Value), strictValue d v = .some v
  | .zero, _ => rfl
  | .succ d, v => by
    cases v with
    | unit => rfl
    | scalar sc =>
      cases sc
      unfold strictValue
      dsimp only
      rw [strictBits_eq, strictBits_eq]
    | ptr p sz =>
      cases p
      unfold strictValue
      dsimp only
      rw [strictBits_eq, strictBits_eq, strictBits_eq]
    | aggregate v fs =>
      unfold strictValue
      rw [strictBits_eq, mapStrictList_eq (strictValue d) (strictValue_eq d) fs]

@[reducible]
def strictValueTop (v : Value) : Value :=
  match strictValue 16 v with
  | .some v' => v'
  | .none => v

@[simp]
theorem strictValueTop_eq (v : Value) : strictValueTop v = v := by
  unfold strictValueTop
  rw [strictValue_eq 16 v]

@[reducible]
def strictSlotsAt (argCount idx : Nat) : List LocalSlot → Option (List LocalSlot)
  | .nil => .some .nil
  | .dead :: rest =>
    match strictSlotsAt argCount (.succ idx) rest with
    | .some rest' => .some (.dead :: rest')
    | .none => .none
  | .uninit :: rest =>
    match strictSlotsAt argCount (.succ idx) rest with
    | .some rest' => .some (.uninit :: rest')
    | .none => .none
  | .init v :: rest =>
    match Bool.and (Nat.ble 1 idx) (Nat.ble idx argCount) with
    | true =>
      match strictSlotsAt argCount (.succ idx) rest with
      | .some rest' => .some (.init v :: rest')
      | .none => .none
    | false =>
      match strictValue 16 v, strictSlotsAt argCount (.succ idx) rest with
      | .some v', .some rest' => .some (.init v' :: rest')
      | _, _ => .none

theorem strictSlotsAt_eq (argCount : Nat) :
    ∀ (idx : Nat) (ls : List LocalSlot), strictSlotsAt argCount idx ls = .some ls
  | _, .nil => rfl
  | idx, slot :: rest => by
    cases slot with
    | dead =>
      unfold strictSlotsAt
      rw [strictSlotsAt_eq argCount (.succ idx) rest]
    | uninit =>
      unfold strictSlotsAt
      rw [strictSlotsAt_eq argCount (.succ idx) rest]
    | init v =>
      unfold strictSlotsAt
      cases Bool.and (Nat.ble 1 idx) (Nat.ble idx argCount) <;> dsimp only
      · rw [strictValue_eq 16 v, strictSlotsAt_eq argCount (.succ idx) rest]
      · rw [strictSlotsAt_eq argCount (.succ idx) rest]

@[reducible]
def strictFrame (argCount : Nat) (f : StackFrame) : Option StackFrame :=
  match strictBits 16 f.blockIdx, strictBits 16 f.stmtIdx, strictSlotsAt argCount 0 f.locals with
  | .some blk, .some idx, .some locs =>
    .some { blockIdx := blk, stmtIdx := idx, locals := locs }
  | _, _, _ => .none

theorem strictFrame_eq (argCount : Nat) (f : StackFrame) :
    strictFrame argCount f = .some f := by
  cases f
  unfold strictFrame
  dsimp only
  rw [strictBits_eq, strictBits_eq, strictSlotsAt_eq]

/--
Force the outer `CapturedMir.mk` constructor head in O(1) without traversing
any static MIR payloads (`basicBlocks`, `localDecls`, `layouts`, `allocations`,
`fnAbi`, etc.).

Call-by-name `whnf` leak prevention: when an inline callee returns, `MirSemantics`
sets `Memory.activeCallee := .some sf.callerBody`. Leaving `sf.callerBody` or
`m.activeCallee` unforced keeps a projection thunk `SavedCallerFrame.callerBody s_prev`
that retains the entire prior `MachineState`, causing exponential blowup across
multi-iteration inline-call loops (`loop -> mid -> leaf`). Matching the outer
`CapturedMir.mk` constructor collapses that projection immediately to the static
body record while leaving every field payload untouched.
-/
@[reducible]
def strictCapturedMirHead (b : CapturedMir) : Option CapturedMir :=
  CapturedMir.casesOn (motive := fun _ => Option CapturedMir) b
    (fun defPath phase role argCount localDecls basicBlocks fnAbi layouts allocations
        typeParamCount genericParams traitImpls =>
      .some (.mk defPath phase role argCount localDecls basicBlocks fnAbi layouts allocations
        typeParamCount genericParams traitImpls))

theorem strictCapturedMirHead_eq (b : CapturedMir) : strictCapturedMirHead b = .some b :=
  rfl

/-- Spine-normalize `Option CapturedMir` by forcing the outer `CapturedMir.mk`
constructor head on `.some b` without traversing static payloads. -/
@[reducible]
def strictOptCapturedMirHead : Option CapturedMir → Option (Option CapturedMir)
  | .none => .some .none
  | .some b =>
    match strictCapturedMirHead b with
    | .some b' => .some (.some b')
    | .none => .none

theorem strictOptCapturedMirHead_eq :
    ∀ (o : Option CapturedMir), strictOptCapturedMirHead o = .some o
  | .none => rfl
  | .some _ => rfl

/--
Spine-normalize a suspended caller frame on `Memory.callStack`.

The caller `StackFrame` is normalized with `strictFrame cb'.argCount`
(NOT `strictFrame 0`), matching `stepMirStateStrict`'s `callee.argCount` /
`body.argCount` invariant: caller parameter slots `1 ≤ idx ≤ argCount` are left
untouched so open-term calls with unused symbolic caller parameters never stall
on `strictBits 128 x` in WHNF while the caller frame is suspended. The outer
`CapturedMir.mk` head of `sf.callerBody` is forced in O(1) via
`strictCapturedMirHead` to prevent `SavedCallerFrame.callerBody` projection
thunks from retaining prior `MachineState`s across repeated inline calls, while
preserving all static body fields verbatim.
-/
@[reducible]
def strictSavedCallerFrame (sf : SavedCallerFrame) : Option SavedCallerFrame :=
  match strictCapturedMirHead sf.callerBody with
  | .none => .none
  | .some cb' =>
    match strictFrame cb'.argCount sf.frame, strictPlace sf.destination,
        strictBits 16 sf.returnTarget, strictOptNat sf.callerProtector with
    | .some fr', .some dest', .some rt', .some cp' =>
      match mapStrictList (strictBits 32) sf.calleeProtectors,
          strictUnwindAction sf.returnUnwind, strictBool sf.isDiverging with
      | .some cps', .some ru', .some div' =>
        .some
          { callerBody := cb'
            frame := fr'
            destination := dest'
            returnTarget := rt'
            callerProtector := cp'
            calleeProtectors := cps'
            returnUnwind := ru'
            isDiverging := div' }
      | _, _, _ => .none
    | _, _, _, _ => .none

theorem strictSavedCallerFrame_eq (sf : SavedCallerFrame) :
    strictSavedCallerFrame sf = .some sf := by
  cases sf
  unfold strictSavedCallerFrame
  dsimp only
  rw [strictFrame_eq, strictPlace_eq, strictBits_eq, strictOptNat_eq,
      mapStrictList_eq (strictBits 32) (strictBits_eq 32),
      strictUnwindAction_eq, strictBool_eq]

/-- Spine-normalize every suspended caller frame on `Memory.callStack`. -/
@[reducible]
def strictCallStack : List SavedCallerFrame → Option (List SavedCallerFrame)
  | .nil => .some .nil
  | sf :: rest =>
    match strictSavedCallerFrame sf, strictCallStack rest with
    | .some sf', .some rest' => .some (sf' :: rest')
    | _, _ => .none

theorem strictCallStack_eq :
    ∀ (cs : List SavedCallerFrame), strictCallStack cs = .some cs
  | .nil => rfl
  | sf :: rest => by
    unfold strictCallStack
    rw [strictSavedCallerFrame_eq sf, strictCallStack_eq rest]

/-- Spine-normalize a reified function-pointer table entry (collapsing
`nextFnPtrAllocId` arithmetic thunks from `internFnPtr`) while keeping the
static `defPath`. -/
@[reducible]
def strictFnPtrEntry (e : FnPtrEntry) : Option FnPtrEntry :=
  match strictBits 64 e.allocId, strictList e.typeArgs, strictOpt e.fnSig with
  | .some aid', .some targs', .some sig' =>
    .some { allocId := aid', defPath := e.defPath, typeArgs := targs', fnSig := sig' }
  | _, _, _ => .none

theorem strictFnPtrEntry_eq (e : FnPtrEntry) : strictFnPtrEntry e = .some e := by
  cases e
  unfold strictFnPtrEntry
  dsimp only
  rw [strictBits_eq, strictList_eq, strictOpt_eq]

@[reducible]
def strictMemory (m : Memory) : Option Memory :=
  match strictBits 32 m.nextAllocId, strictList m.globals, strictBorrows m.borrows, strictBits 32 m.nextTag with
  | .some naid, .some glob, .some bor, .some nt =>
    match strictList m.callees, strictList m.traitImpls, strictCallStack m.callStack,
        strictOptCapturedMirHead m.activeCallee with
    | .some cal, .some ti, .some cs, .some ac =>
      match mapStrictList (strictBits 32) m.activeProtectors, strictBits 32 m.nextProtector,
          strictSlotsAt 0 0 m.callerLocals with
      | .some ap, .some np, .some cl =>
        match mapStrictList strictFnPtrEntry m.fnPtrs, mapStrictList (strictBits 64) m.exposedAllocIds,
            strictBool m.rootUnwindCeiling with
        | .some fp, .some ea, .some ruc =>
          .some
            { nextAllocId := naid, globals := glob, borrows := bor, nextTag := nt,
              callees := cal, traitImpls := ti, callStack := cs, activeCallee := ac,
              activeProtectors := ap, nextProtector := np, callerLocals := cl,
              fnPtrs := fp, exposedAllocIds := ea,
              rootUnwindCeiling := ruc }
        | _, _, _ => .none
      | _, _, _ => .none
    | _, _, _, _ => .none
  | _, _, _, _ => .none

theorem strictMemory_eq (m : Memory) : strictMemory m = .some m := by
  cases m
  unfold strictMemory
  dsimp only
  rw [strictBits_eq, strictList_eq, strictBorrows_eq, strictBits_eq,
      strictList_eq, strictList_eq, strictCallStack_eq, strictOptCapturedMirHead_eq,
      mapStrictList_eq (strictBits 32) (strictBits_eq 32), strictBits_eq, strictSlotsAt_eq,
      mapStrictList_eq strictFnPtrEntry strictFnPtrEntry_eq,
      mapStrictList_eq (strictBits 64) (strictBits_eq 64),
      strictBool_eq]

@[reducible]
def strictMachineState (argCount : Nat) (s : MachineState) : Option MachineState :=
  match strictFrame argCount s.frame, strictMemory s.memory with
  | .some f', .some m' => .some { frame := f', memory := m' }
  | _, _ => .none

theorem strictMachineState_eq (argCount : Nat) (s : MachineState) :
    strictMachineState argCount s = .some s := by
  cases s
  unfold strictMachineState
  dsimp only
  rw [strictFrame_eq, strictMemory_eq]

/--
Spine-normalizing wrapper around `stepMirState` for closed-term `by rfl`
checkers.
-/
@[reducible]
def stepMirStateStrict (body : CapturedMir) (st : MirExecState) : MirStepNode :=
  match st with
  | .running s =>
    match
      strictMachineState
        (match s.memory.activeCallee with
         | .some callee => callee.argCount
         | .none => body.argCount)
        s
    with
    | .some s' => stepMirState body (.running s')
    | .none => stepMirState body st
  | _ => stepMirState body st

@[simp]
theorem stepMirStateStrict_eq (body : CapturedMir) (st : MirExecState) :
    stepMirStateStrict body st = stepMirState body st := by
  cases st with
  | running s =>
    unfold stepMirStateStrict
    dsimp only
    rw [strictMachineState_eq _ s]
  | halted _ => rfl
  | faulted _ => rfl

/--
Periodic spine-normalizing wrapper around `stepMirState`: normalizes concrete
`MachineState` spines once every 2 steps (`Nat.beq (fuel' % 2) 0`), keeping
call-by-name kernel reduction linear in MIR length (even across back-to-back
`AddWithOverflow` + `assert` + deref-write chains that blow up after 3
unnormalized steps) with compact kernel `Expr` arenas and minimal overhead on
short symbolic companions.
-/
@[reducible]
def stepMirStatePeriodic (fuel' : Nat) (body : CapturedMir) (st : MirExecState) : MirStepNode :=
  match Nat.beq (fuel' % 2) 0 with
  | false => stepMirState body st
  | true => stepMirStateStrict body st

@[simp]
theorem stepMirStatePeriodic_eq (fuel' : Nat) (body : CapturedMir) (st : MirExecState) :
    stepMirStatePeriodic fuel' body st = stepMirState body st := by
  unfold stepMirStatePeriodic
  cases Nat.beq (fuel' % 2) 0 <;> simp only [stepMirStateStrict_eq]



end Anneal.ClosureFnPtrTests.V08Strict

namespace Anneal.ClosureFnPtrTests.V08

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! ### Harness -/

/-- Outcome of a bounded run of `stepMirState`. -/
inductive RunTag : Type where
  | normalScalar (bits sizeBytes : Nat)
  | normalOther
  | panic
  | abort
  | ub
  | unsupported
  | ext (defPath : String)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Run `body` from `st` for at most `fuel` steps of the trusted stepper
`stepMirState`, through its spine-normalizing wrapper `stepMirStatePeriodic`
(`stepMirStatePeriodic_eq` proves it equal to `stepMirState`), which keeps
closed-term kernel evaluation linear. -/
def run (fuel : Nat) (body : CapturedMir) (st : MirExecState) : RunTag :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match Anneal.ClosureFnPtrTests.V08Strict.stepMirStatePeriodic fuel' body st with
    | .ret (.normal (.scalar sc, _)) => .normalScalar sc.bits sc.sizeBytes
    | .ret (.normal _) => .normalOther
    | .ret .panic => .panic
    | .ret .abort => .abort
    | .tau st' => run fuel' body st'
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | .vis (.inl (.fail .outOfFuel)) _ => .outOfFuel
    | .vis (.inr (.inl _)) k => run fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => .ext req.defPath

/-- `run` steps exactly like the trusted `stepMirState`. -/
theorem run_step_eq (fuel' : Nat) (body : CapturedMir) (st : MirExecState) :
    Anneal.ClosureFnPtrTests.V08Strict.stepMirStatePeriodic fuel' body st = stepMirState body st :=
  Anneal.ClosureFnPtrTests.V08Strict.stepMirStatePeriodic_eq fuel' body st

/-- Root memory linking `callees` and the reified function pointers `fnPtrs`. -/
def memWith (body : CapturedMir) (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) : Memory :=
  { emptyMemory with
    nextAllocId := length body.allocations
    globals := body.allocations
    callees := callees
    traitImpls := body.traitImpls
    fnPtrs := fnPtrs }

/-- Run `body` on `args` with linked `callees` and function pointers `fnPtrs`. -/
def runWith (body : CapturedMir) (args : List Value) (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) : RunTag :=
  run 400 body
    (.running
      { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocalsAux 0 body.localDecls args }
        memory := memWith body callees fnPtrs })

/-- A `u32` value. -/
def u32v (n : Nat) : Value := .scalar ⟨n, 4⟩

-- Synthetic stand-in for the `core::fmt::Arguments` constructor `defPath`,
-- linked only by `miri-difftest` oracle modules. The caller has already
-- evaluated the `&'static str` argument; this body returns that message slice
-- as the constructed `Arguments`, which the caller passes to
-- `core::panicking::panic_fmt`.
def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=
  { defPath := defPath
    phase := MirPhaseTag.runtimePostCleanup
    role := ContractRole.model
    argCount := 1
    localDecls :=
      [{ mutability := Mutability.mut, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none },
       { mutability := Mutability.not, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none }]
    basicBlocks :=
      [{ statements :=
           [{ kind := StatementKind.assign { local_ := 0, projection := [] }
                (Rvalue.use (Operand.copy { local_ := 1, projection := [] })),
              span := "<dummy>" }]
         terminator := { kind := TerminatorKind.return_, span := "<dummy>" }
         isCleanup := false }]
    fnAbi :=
      { args := [{ layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }]
        ret := { layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }
        conv := CallConv.rust
        canUnwind := false }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [{ size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }] }
    allocations := [] }

/-- `core::fmt::Arguments` constructor stubs linked by `miri-difftest`. -/
def fmtStubs : List CapturedMir :=
  [fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::new_const",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::new_const"]

/-- Replace the unwind action of the call terminating `bb0`. -/
def setBb0CallUnwind (b : CapturedMir) (u : UnwindAction) : CapturedMir :=
  match b.basicBlocks with
  | bb :: rest =>
    match bb.terminator.kind with
    | .call f a d t _ =>
      { b with
        basicBlocks :=
          { bb with terminator := { bb.terminator with kind := .call f a d t u } } :: rest }
    | _ => b
  | .nil => b

/-! ### Fixture vocabulary -/

def u32K : RigidTy := .uint .u32
def fnU32 : RigidTy := .fnPtr [u32K] u32K .safe .rust
def ufnU32 : RigidTy := .fnPtr [u32K] u32K .unsafe_ .rust
def sharedPath : String := "closure_matrix::fn_shared::{closure#0}"
def capPath : String := "closure_matrix::capturing_direct::{closure#0}"
def capZstPath : String := "closure_matrix::capturing_direct::{closure#1}"
def genericPath : String := "closure_matrix::generic_closure::{closure#0}"
def sharedClo : RigidTy := .closure sharedPath .nil
def capClo : RigidTy := .closure capPath [u32K]
def capZstClo : RigidTy := .closure capZstPath [.tuple .nil]
def plc (l : Nat) : Place := { local_ := l, projection := .nil }
def decl (k : RigidTy) (idx : Nat) : LocalDecl :=
  { mutability := .mut, ty := { kind := k, layoutIdx := idx }, debugName := .none }
/-- Function-pointer value at synthetic allocation `65536`. -/
def fnPtrVal : Value := .ptr { allocId := 65536, offsetBytes := 0 } 8
/-- Environment value passed explicitly by forged or direct calls. -/
def envScalar : Value := .scalar ⟨1, 8⟩
/-- `FnPtrEntry` at `65536` naming `p` with signature `sig`. -/
def entry (p : String) (sig : RigidTy) : FnPtrEntry :=
  { allocId := 65536, defPath := p, fnSig := .some sig }
def retBlock : BasicBlockData :=
  { statements := .nil, terminator := { kind := .return_, span := "ret" }, isCleanup := false }

/-- `fn(_1 : sigKind, _2 : argKind) -> u32 { _0 = _1(_2) }` -/
def ptrCaller (sigKind : RigidTy) (argKind : RigidTy := u32K) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::ptr_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl sigKind 1, decl argKind 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .call (.copy (plc 1)) [.copy (plc 2)] (plc 0) (.some 1) .continue_
             span := "ptr_call" }
         isCleanup := false },
       retBlock] }

/-- `fn(_1 : sigKind, _2 : envKind, _3 : u32) -> u32 { _0 = _1(_2, _3) }`: a forged
`(N + 1)`-argument call passing the closure environment explicitly. -/
def envPtrCaller (sigKind envKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::env_ptr_caller"
    argCount := 3
    localDecls := [decl u32K 0, decl sigKind 1, decl envKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .call (.copy (plc 1)) [.copy (plc 2), .copy (plc 3)] (plc 0) (.some 1) .continue_
             span := "env_ptr_call" }
         isCleanup := false },
       retBlock] }

/-- `fn(_1 : envKind, _2 : u32) -> u32 { _0 = p(_1, _2) }`: a direct
(`isIndirect = false`) call of the closure body `p` passing its environment. -/
def directEnvCaller (p : String) (envKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::direct_env_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl envKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind :=
               .call (.constant { ty := { kind := .fnDef p .nil, layoutIdx := 2 }, val := .zeroSized })
                 [.copy (plc 1), .copy (plc 2)] (plc 0) (.some 1) .continue_
             span := "direct_env_call" }
         isCleanup := false },
       retBlock] }

/-- The `fn_shared` closure body forged to read the field `(*_1).0` of its
(zero-sized) environment. -/
def forgedEnvReadBody : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared_closure_0.body with
    basicBlocks :=
      [{ statements :=
           [{ kind :=
                .assign (plc 0)
                  (.use (.copy { local_ := 1
                                 projection := [.deref, .field 0 { kind := u32K, layoutIdx := 0 }] }))
              span := "forged_env_read" }]
         terminator := { kind := .return_, span := "ret" }
         isCleanup := false }] }

/-- Contrast for `forgedEnvReadBody`: the same forged body reading its argument
`_2` instead of its environment returns normally. -/
def forgedArgReadBody : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared_closure_0.body with
    basicBlocks :=
      [{ statements :=
           [{ kind := .assign (plc 0) (.use (.copy (plc 2))), span := "forged_arg_read" }]
         terminator := { kind := .return_, span := "ret" }
         isCleanup := false }] }

/-- Type arguments of `const_eval_select::<(u32,), ct_add, G, u32>`. -/
def cesTyArgs (rtKind : RigidTy) : List RigidTy :=
  [.tuple [u32K], .fnDef "closure_matrix::ct_add" .nil, rtKind, u32K]

/-- `fn(_1 : u32, _2 : rtKind) -> u32 { StorageLive(_3); _3 = (copy _1,); _0 = const_eval_select(move _3, ct_add, copy _2) }`:
an inline `core::intrinsics::const_eval_select` call with runtime target `_2`. -/
def cesCaller (rtKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::ces_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl u32K 0, decl rtKind 1, decl (.tuple [u32K]) 0]
    basicBlocks :=
      [{ statements :=
           [{ kind := .storageLive 3, span := "ces_live" },
            { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
         terminator :=
           { kind :=
               .call
                 (.constant
                   { ty := { kind := .fnDef "core::intrinsics::const_eval_select" (cesTyArgs rtKind)
                             layoutIdx := 2 }
                     val := .zeroSized })
                 [.move (plc 3),
                  .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                              val := .zeroSized },
                  .copy (plc 2)]
                 (plc 0) (.some 1) .continue_
             span := "ces_call" }
         isCleanup := false },
       retBlock] }

/-- Outcome of `evalReifyFnPointer` on a single operand local. -/
inductive CoerceTag : Type where
  | ok
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Reify local `_0 : opKind` holding `v` to `target` via coercion tag `ck`. -/
def coerce (ck : String) (opKind : RigidTy) (v : Value) (target : RigidTy)
    (callees : List CapturedMir) : CoerceTag :=
  match
    evalReifyFnPointer [.init v] (.move (plc 0)) { kind := target, layoutIdx := 1 }
      { emptyMemory with callees := callees } [decl opKind 2] V08.Mir.ClosureMatrix.fn_shared.layouts ck
  with
  | .ok _ _ _ => .ok
  | .ub => .ub
  | .unsupported => .unsupported

/-- Three-way classification of the captured closure bodies by their own `_1`. -/
theorem closure_shapes :
    (calleeOwnClosureShape? V08.Mir.ClosureMatrix.fn_shared_closure_0.body, calleeOwnClosureShape? V08.Mir.ClosureMatrix.fn_mut_kind_closure_0.body, calleeOwnClosureShape? V08.Mir.ClosureMatrix.fn_once_kind_closure_0.body, calleeOwnClosureShape? V08.Mir.ClosureMatrix.capturing_direct_closure_0.body, calleeOwnClosureShape? V08.Mir.ClosureMatrix.capturing_direct_closure_1.body, calleeOwnClosureShape? V08.Mir.ClosureMatrix.fn_shared.body, calleeOwnClosureShape? V08.Mir.ClosureMatrix.id_mut.body) =
      (.some (.nonCapturing .sharedRef), .some (.nonCapturing .mutRef), .some (.nonCapturing .byValue), .some .capturing, .some .capturing, .none, .none) := by
  rfl

/-- C10 contrast: the unmodified function-pointer check alone would admit the forged `(N + 1)`-argument call; the closure-aware `checkCalleeTargetCompatible` rejects it. -/
theorem forged_env_call_passes_unmodified_fn_ptr_check :
    (checkFnPtrTargetCompatible { defPath := sharedPath, fnSig := .some (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust), isIndirect := true } V08.Mir.ClosureMatrix.fn_shared_closure_0.body 2, checkCalleeTargetCompatible { defPath := sharedPath, fnSig := .some (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust), isIndirect := true } V08.Mir.ClosureMatrix.fn_shared_closure_0.body 2) =
      (true, false) := by
  rfl

/-- C11: direct targets are compatible and enter with unchanged arguments, even for closure bodies. -/
theorem direct_target_skips_closure_gate :
    (checkCalleeTargetCompatible { defPath := sharedPath, isIndirect := false } V08.Mir.ClosureMatrix.fn_shared_closure_0.body 2, calleeEntryArgs { defPath := sharedPath, isIndirect := false } V08.Mir.ClosureMatrix.fn_shared_closure_0.body [envScalar, u32v 5]) =
      (true, [envScalar, u32v 5]) := by
  rfl

/-- Indirect targets prepend `.scalar ⟨1, 8⟩` (`&`, `&mut`) or `.aggregate 0 []` (by value). -/
theorem indirect_target_prepends_env :
    (calleeEntryArgs { defPath := sharedPath, isIndirect := true } V08.Mir.ClosureMatrix.fn_shared_closure_0.body [u32v 5], calleeEntryArgs { defPath := "closure_matrix::fn_once_kind::{closure#0}", isIndirect := true } V08.Mir.ClosureMatrix.fn_once_kind_closure_0.body [u32v 5]) =
      ([.scalar ⟨1, 8⟩, u32v 5], [.aggregate 0 .nil, u32v 5]) := by
  rfl

/-- `ClosureFnPointer(Safe)` to `fn(u32) -> u32`. -/
theorem coerce_safe_ok :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ok := by
  rfl

/-- `ClosureFnPointer(Unsafe)` to `unsafe fn(u32) -> u32`. -/
theorem coerce_unsafe_ok :
    coerce "ClosureFnPointer(Unsafe)" sharedClo (.aggregate 0 .nil) ufnU32 [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ok := by
  rfl

/-- Safety mismatch: `ClosureFnPointer(Safe)` to an `unsafe fn` pointer. -/
theorem coerce_safe_to_unsafe_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) ufnU32 [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Safety mismatch: `ClosureFnPointer(Unsafe)` to a safe `fn` pointer. -/
theorem coerce_unsafe_to_safe_is_ub :
    coerce "ClosureFnPointer(Unsafe)" sharedClo (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- A capturing (`u32`) closure value never coerces. -/
theorem coerce_capturing_is_ub :
    coerce "ClosureFnPointer(Safe)" capClo (.aggregate 0 [u32v 7]) fnU32 [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body] =
      .ub := by
  rfl

/-- A capturing (`()`) closure value never coerces. -/
theorem coerce_zst_capturing_is_ub :
    coerce "ClosureFnPointer(Safe)" capZstClo (.aggregate 0 [.unit]) fnU32 [V08.Mir.ClosureMatrix.capturing_direct_closure_1.body] =
      .ub := by
  rfl

/-- A capturing (`()`) closure type never coerces, even with an empty value. -/
theorem coerce_zst_capturing_empty_value_is_ub :
    coerce "ClosureFnPointer(Safe)" capZstClo (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.capturing_direct_closure_1.body] =
      .ub := by
  rfl

/-- Closures coerce only to Rust-ABI pointers. -/
theorem coerce_extern_c_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K] u32K .safe .c) [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Signature arity mismatch. -/
theorem coerce_arity_mismatch_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K, u32K] u32K .safe .rust) [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Parameter type mismatch. -/
theorem coerce_param_mismatch_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [.uint .u64] u32K .safe .rust) [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Return type mismatch. -/
theorem coerce_return_mismatch_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K] (.uint .u64) .safe .rust) [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- C5: a generic closure body is `.unsupported`, never `.ub`. -/
theorem coerce_generic_is_unsupported :
    coerce "ClosureFnPointer(Safe)" (.closure genericPath .nil) (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .unsupported := by
  rfl

/-- A capturing closure body linked under a non-capturing closure type is `.ub`. -/
theorem coerce_linked_capturing_body_is_ub :
    coerce "ClosureFnPointer(Safe)" (.closure capPath .nil) (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body] =
      .ub := by
  rfl

/-- A non-closure body linked under the closure path is `.ub`. -/
theorem coerce_non_closure_body_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [{ V08.Mir.ClosureMatrix.helper_triple.body with defPath := sharedPath }] =
      .ub := by
  rfl

/-- An unlinked closure body coerces (calls are then external). -/
theorem coerce_unlinked_ok :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [] =
      .ok := by
  rfl

/-- The pre-fix `args.types()` closure encoding never coerces. -/
theorem coerce_legacy_encoding_is_ub :
    coerce "ClosureFnPointer(Safe)" (.closure sharedPath [.int .i8, .fnPtr [.tuple [u32K]] u32K .safe (.other "rust-call"), .tuple .nil]) (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- Function-item reification is unchanged. -/
theorem reify_fn_item_still_ok :
    coerce "ReifyFnPointer(Safe)" (.fnDef "closure_matrix::helper_triple" .nil) .unit fnU32 [V08.Mir.ClosureMatrix.helper_triple.body] =
      .ok := by
  rfl

/-- `Fn` closure (`_1 : &{closure}`) reified with `ClosureFnPointer(Safe)` and called: `5 + 17`. -/
theorem fn_shared_is_22 :
    runWith V08.Mir.ClosureMatrix.fn_shared.body [u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- `FnMut` closure (`_1 : &mut {closure}`), passed through the generic `id_mut` first. -/
theorem fn_mut_kind_is_7 :
    runWith V08.Mir.ClosureMatrix.fn_mut_kind.body [u32v 5] [V08.Mir.ClosureMatrix.id_mut.body, V08.Mir.ClosureMatrix.fn_mut_kind_closure_0.body] =
      .normalScalar 7 4 := by
  rfl

/-- `FnOnce` closure (`_1 : {closure}` by value), passed through the generic `id_once` first. -/
theorem fn_once_kind_is_8 :
    runWith V08.Mir.ClosureMatrix.fn_once_kind.body [u32v 5] [V08.Mir.ClosureMatrix.id_once.body, V08.Mir.ClosureMatrix.fn_once_kind_closure_0.body] =
      .normalScalar 8 4 := by
  rfl

/-- Zero-argument closure (`argCount = 1`, environment only). -/
theorem zero_arg_is_7 :
    runWith V08.Mir.ClosureMatrix.zero_arg.body [] [V08.Mir.ClosureMatrix.zero_arg_closure_0.body] =
      .normalScalar 7 4 := by
  rfl

/-- Two-argument closure: `6 ^ 3`. -/
theorem two_arg_is_5 :
    runWith V08.Mir.ClosureMatrix.two_arg.body [u32v 6, u32v 3] [V08.Mir.ClosureMatrix.two_arg_closure_0.body] =
      .normalScalar 5 4 := by
  rfl

/-- `ClosureFnPointer(Unsafe)` to an `unsafe fn` pointer, called in `unsafe`: `5 ^ 17`. -/
theorem unsafe_closure_is_20 :
    runWith V08.Mir.ClosureMatrix.unsafe_closure.body [u32v 5] [V08.Mir.ClosureMatrix.unsafe_closure_closure_0.body] =
      .normalScalar 20 4 := by
  rfl

/-- `UnsafeFnPointer` widening keeps the pointer: `FnPtrToPtr` of both pointers compare equal (`raw_c == raw_d`), `(5 + 1) ^ (1 << 8)`. -/
theorem widen_and_identity_is_262 :
    runWith V08.Mir.ClosureMatrix.widen_and_identity.body [u32v 5] [V08.Mir.ClosureMatrix.widen_and_identity_closure_0.body] =
      .normalScalar 262 4 := by
  rfl

/-- A function item and a closure reified side by side: `(4 * 3) ^ (4 * 5)`. -/
theorem mixed_fn_item_and_closure_is_24 :
    runWith V08.Mir.ClosureMatrix.mixed_fn_item_and_closure.body [u32v 4] [V08.Mir.ClosureMatrix.helper_triple.body, V08.Mir.ClosureMatrix.mixed_fn_item_and_closure_closure_0.body] =
      .normalScalar 24 4 := by
  rfl

/-- `TerminatorKind.tailCall` (`become f(x)`) through a closure pointer: `9 ^ 5`. -/
theorem tail_call_is_12 :
    runWith V08.Mir.ClosureMatrix.tail_through_closure.body [u32v 9] [V08.Mir.ClosureMatrix.tail_through_closure_closure_0.body] =
      .normalScalar 12 4 := by
  rfl

/-- Diverging call (`target = none`) of a `fn(u32) -> !` closure pointer whose body panics. -/
theorem diverging_call_panics :
    runWith V08.Mir.ClosureMatrix.diverging_closure.body [u32v 0] ([V08.Mir.ClosureMatrix.diverging_closure_closure_0.body] ++ fmtStubs) =
      .panic := by
  rfl

/-- The same function when the diverging call is not reached. -/
theorem diverging_call_not_taken_is_3 :
    runWith V08.Mir.ClosureMatrix.diverging_closure.body [u32v 3] ([V08.Mir.ClosureMatrix.diverging_closure_closure_0.body] ++ fmtStubs) =
      .normalScalar 3 4 := by
  rfl

/-- `UnwindAction.cleanup`: the closure panics, the caller drops its guard in the cleanup block and resumes unwinding. -/
theorem unwind_cleanup_panics :
    runWith V08.Mir.ClosureMatrix.unwind_through_closure.body [u32v 0] ([V08.Mir.ClosureMatrix.unwind_through_closure_closure_0.body, V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .panic := by
  rfl

/-- The same call when the closure returns normally. -/
theorem unwind_cleanup_normal_is_4 :
    runWith V08.Mir.ClosureMatrix.unwind_through_closure.body [u32v 4] ([V08.Mir.ClosureMatrix.unwind_through_closure_closure_0.body, V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .normalScalar 4 4 := by
  rfl

/-- `UnwindAction.continue_` on the closure call: the panic propagates. -/
theorem unwind_continue_panics :
    runWith (setBb0CallUnwind V08.Mir.ClosureMatrix.unwind_through_closure.body .continue_) [u32v 0] ([V08.Mir.ClosureMatrix.unwind_through_closure_closure_0.body, V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .panic := by
  rfl

/-- `UnwindAction.terminate` on the closure call: unwinding aborts. -/
theorem unwind_terminate_aborts :
    runWith (setBb0CallUnwind V08.Mir.ClosureMatrix.unwind_through_closure.body .terminate) [u32v 0] ([V08.Mir.ClosureMatrix.unwind_through_closure_closure_0.body, V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .abort := by
  rfl

/-- `UnwindAction.unreachable` on the closure call: unwinding is undefined behavior. -/
theorem unwind_unreachable_is_ub :
    runWith (setBb0CallUnwind V08.Mir.ClosureMatrix.unwind_through_closure.body .unreachable) [u32v 0] ([V08.Mir.ClosureMatrix.unwind_through_closure_closure_0.body, V08.Mir.ClosureMatrix.Guard_as_core_ops_Drop_drop.body] ++ fmtStubs) =
      .ub := by
  rfl

/-- `const_eval_select` with a closure pointer as runtime target, as captured (rustc lowers it to an indirect call): `4 + 17`. -/
theorem const_eval_select_lowered_is_21 :
    runWith V08.Mir.ClosureMatrix.ces_through_closure_fn_ptr.body [u32v 4] [V08.Mir.ClosureMatrix.ces_through_closure_fn_ptr_closure_0.body] =
      .normalScalar 21 4 := by
  rfl

/-- C5: a closure inside a generic function: the closure type carries no parent generic arguments, so the coercion is `.unsupported` (never `.ub`). -/
theorem generic_closure_is_unsupported :
    runWith V08.Mir.ClosureMatrix.call_generic.body [u32v 77] [V08.Mir.ClosureMatrix.generic_closure.body, V08.Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .unsupported := by
  rfl

/-- C11: a direct closure call goes through `<{closure} as Fn<(u32,)>>::call` (`isIndirect = false`) and stays an external call (no false `.ub`). -/
theorem direct_fn_trait_call_is_external :
    runWith V08.Mir.ClosureMatrix.direct_closure_call.body [u32v 1] [V08.Mir.ClosureMatrix.direct_closure_call_closure_0.body] =
      .ext "core::ops::Fn::call" := by
  rfl

/-- Without the closure body the coercion succeeds and the call is external (never `.ub`). -/
theorem unlinked_closure_is_external :
    runWith V08.Mir.ClosureMatrix.fn_shared.body [u32v 5] [] =
      .ext "closure_matrix::fn_shared::{closure#0}" := by
  rfl

/-- Callee-directed dispatch: a pointer to the closure that never went through a coercion in this run is entered with the synthesized environment. -/
theorem untagged_closure_pointer_dispatches :
    runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath fnU32] =
      .normalScalar 22 4 := by
  rfl

/-- C10: a forged `(N + 1)`-argument pointer `fn(&{closure}, u32) -> u32` to a non-capturing closure body is `.ub`. -/
theorem forged_env_call_non_capturing_is_ub :
    runWith (envPtrCaller (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust) (.ref .not sharedClo)) [fnPtrVal, envScalar, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10: a forged `(N + 1)`-argument pointer to a capturing (`u32`) closure body is `.ub`. -/
theorem forged_env_call_capturing_is_ub :
    runWith (envPtrCaller (.fnPtr [.ref .not capClo, u32K] u32K .safe .rust) (.ref .not capClo)) [fnPtrVal, envScalar, u32v 5] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body] [entry capPath (.fnPtr [.ref .not capClo, u32K] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10: a forged `(N + 1)`-argument pointer to a capturing (`()`) closure body is `.ub`. -/
theorem forged_env_call_zst_capturing_is_ub :
    runWith (envPtrCaller (.fnPtr [.ref .not capZstClo, u32K] u32K .safe .rust) (.ref .not capZstClo)) [fnPtrVal, envScalar, u32v 5] [V08.Mir.ClosureMatrix.capturing_direct_closure_1.body] [entry capZstPath (.fnPtr [.ref .not capZstClo, u32K] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10: an `N`-argument pointer to a capturing closure body is `.ub` (no environment can be synthesized). -/
theorem pointer_to_capturing_closure_is_ub :
    runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body] [entry capPath fnU32] =
      .ub := by
  rfl

/-- A pointer to the closure transmuted to `fn(u64) -> u32` is `.ub`. -/
theorem transmuted_signature_is_ub :
    runWith (ptrCaller (.fnPtr [.uint .u64] u32K .safe .rust) (.uint .u64)) [fnPtrVal, .scalar ⟨5, 8⟩] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [.uint .u64] u32K .safe .rust)] =
      .ub := by
  rfl

/-- A pointer to the closure with the `extern "C"` ABI is `.ub`. -/
theorem extern_c_pointer_is_ub :
    runWith (ptrCaller (.fnPtr [u32K] u32K .safe .c)) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [u32K] u32K .safe .c)] =
      .ub := by
  rfl

/-- C11: a direct (`isIndirect = false`) call of the linked closure body passing its environment explicitly is entered unchanged. -/
theorem direct_env_call_succeeds :
    runWith (directEnvCaller sharedPath (.ref .not sharedClo)) [envScalar, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- A forged non-capturing closure body that reads `(*_1).0` faults: the synthesized environment has no provenance. -/
theorem forged_env_read_is_ub :
    runWith V08.Mir.ClosureMatrix.fn_shared.body [u32v 5] [forgedEnvReadBody] =
      .ub := by
  rfl

/-- Contrast: the same forged body reading its argument `_2` returns normally, so the fault above comes from the environment read. -/
theorem forged_arg_read_contrast_is_5 :
    runWith V08.Mir.ClosureMatrix.fn_shared.body [u32v 5] [forgedArgReadBody] =
      .normalScalar 5 4 := by
  rfl

/-- Inline `const_eval_select` with a closure pointer as runtime target: dispatched with the synthesized environment. -/
theorem inline_ces_indirect_closure_is_22 :
    runWith (cesCaller fnU32) [u32v 5, fnPtrVal] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath fnU32] =
      .normalScalar 22 4 := by
  rfl

/-- Inline `const_eval_select` with a non-capturing closure value as runtime target. -/
theorem inline_ces_direct_closure_is_22 :
    runWith (cesCaller sharedClo) [u32v 5, .aggregate 0 .nil] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- Inline `const_eval_select` with a capturing closure value as runtime target is `.unsupported` (never `.ub`). -/
theorem inline_ces_direct_capturing_is_unsupported :
    runWith (cesCaller capClo) [u32v 5, .aggregate 0 [u32v 7]] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body] =
      .unsupported := by
  rfl

/-- C5: inline `const_eval_select` with a generic closure body as runtime target is `.unsupported` (never `.ub`). -/
theorem inline_ces_generic_closure_is_unsupported :
    runWith (cesCaller (.closure genericPath .nil)) [u32v 5, .aggregate 0 .nil] [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .unsupported := by
  rfl

/-- C10: inline `const_eval_select` through a pointer to a capturing closure body is `.ub`. -/
theorem inline_ces_indirect_capturing_is_ub :
    runWith (cesCaller fnU32) [u32v 5, fnPtrVal] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body] [entry capPath fnU32] =
      .ub := by
  rfl

/-- Inline `const_eval_select` through an `extern "C"` pointer to the closure is `.ub`. -/
theorem inline_ces_extern_c_is_ub :
    runWith (cesCaller (.fnPtr [u32K] u32K .safe .c)) [u32v 5, fnPtrVal] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [u32K] u32K .safe .c)] =
      .ub := by
  rfl

/-- `fn(_1 : sigKind, _2 : u32) -> ! { _0 = _1(_2) }` (diverging indirect call). -/
def divPtrCaller (sigKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::div_ptr_caller"
    argCount := 2
    localDecls := [decl .never 2, decl sigKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .call (.copy (plc 1)) [.copy (plc 2)] (plc 0) .none .continue_
             span := "div_ptr_call" }
         isCleanup := false }] }

/-- `fn(_1 : sigKind, _2 : u32) -> u32 { become _1(_2) }` (indirect tail call). -/
def tailPtrCaller (sigKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::tail_ptr_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl sigKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .tailCall (.copy (plc 1)) [.copy (plc 2)]
             span := "tail_ptr_call" }
         isCleanup := false }] }

/-- `fn(_1 : sigKind, _2 : envKind, _3 : u32) -> u32 { become _1(_2, _3) }`: forged `(N + 1)`-arg indirect tail call. -/
def tailEnvPtrCaller (sigKind envKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::tail_env_ptr_caller"
    argCount := 3
    localDecls := [decl u32K 0, decl sigKind 1, decl envKind 1, decl u32K 0]
    basicBlocks :=
      [{ statements := .nil
         terminator :=
           { kind := .tailCall (.copy (plc 1)) [.copy (plc 2), .copy (plc 3)]
             span := "tail_env_ptr_call" }
         isCleanup := false }] }

/-- Inline `const_eval_select` carrying `rtKind` solely on the operand local `_2` (`target.typeArgs = []`). -/
def cesOperandTyOnlyCaller (rtKind : RigidTy) : CapturedMir :=
  { V08.Mir.ClosureMatrix.fn_shared.body with
    defPath := "tests::ces_op_ty_only_caller"
    argCount := 2
    localDecls := [decl u32K 0, decl u32K 0, decl rtKind 1, decl (.tuple [u32K]) 0]
    basicBlocks :=
      [{ statements :=
           [{ kind := .storageLive 3, span := "ces_live" },
            { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
         terminator :=
           { kind :=
               .call
                 (.constant
                   { ty := { kind := .fnDef "core::intrinsics::const_eval_select" .nil
                             layoutIdx := 2 }
                     val := .zeroSized })
                 [.move (plc 3),
                  .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                              val := .zeroSized },
                  .copy (plc 2)]
                 (plc 0) (.some 1) .continue_
             span := "ces_call" }
         isCleanup := false },
       retBlock] }

/-- C5: indirect normal call, diverging call, tail call, and indirect `const_eval_select` to a linked generic closure body all report `.unsupported` (never `.ub` or `.ext`). -/
theorem indirect_generic_closure_all_sites_unsupported :
    (runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath fnU32],
     runWith (divPtrCaller (.fnPtr [u32K] .never .safe .rust)) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath (.fnPtr [u32K] .never .safe .rust)],
     runWith (tailPtrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath fnU32],
     runWith (cesCaller fnU32) [u32v 5, fnPtrVal] [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] [entry genericPath fnU32]) =
      (.unsupported, .unsupported, .unsupported, .unsupported) := by
  rfl

/-- Direct `const_eval_select` resolves a non-capturing closure type carried on `operandTy` even when `target.typeArgs` is empty. -/
theorem inline_ces_direct_closure_from_operand_ty_only_is_22 :
    runWith (cesOperandTyOnlyCaller sharedClo) [u32v 5, .aggregate 0 .nil] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .normalScalar 22 4 := by
  rfl

/-- Forged scalar runtime target for a generic closure type in `const_eval_select` faults with `.ub` (never `.unsupported`). -/
theorem inline_ces_forged_scalar_generic_closure_is_ub :
    runWith (cesCaller (.closure genericPath .nil)) [u32v 5, u32v 99] [V08.Mir.ClosureMatrix.generic_closure_closure_0.body] =
      .ub := by
  rfl

/-- Direct `const_eval_select` rejects a non-Rust ABI closure body with `.ub`. -/
theorem inline_ces_direct_non_rust_abi_closure_is_ub :
    let cAbiClosure :=
      { V08.Mir.ClosureMatrix.fn_shared_closure_0.body with
        fnAbi := { V08.Mir.ClosureMatrix.fn_shared_closure_0.body.fnAbi with conv := .c } }
    runWith (cesCaller sharedClo) [u32v 5, .aggregate 0 .nil] [cAbiClosure] =
      .ub := by
  rfl

/-- Inline `const_eval_select` rejects a transmuted `fn(u64) -> u32` pointer to a closure with `.ub`. -/
theorem inline_ces_transmuted_signature_is_ub :
    let caller :=
      { V08.Mir.ClosureMatrix.fn_shared.body with
        defPath := "tests::ces_transmute_caller"
        argCount := 2
        localDecls := [decl u32K 0, decl (.uint .u64) 1, decl (.fnPtr [.uint .u64] u32K .safe .rust) 1, decl (.tuple [.uint .u64]) 1]
        basicBlocks :=
          [{ statements :=
               [{ kind := .storageLive 3, span := "ces_live" },
                { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
             terminator :=
               { kind :=
                   .call
                     (.constant
                       { ty := { kind := .fnDef "core::intrinsics::const_eval_select"
                                   [.tuple [.uint .u64], .fnDef "closure_matrix::ct_add" .nil, .fnPtr [.uint .u64] u32K .safe .rust, u32K]
                                 layoutIdx := 2 }
                         val := .zeroSized })
                     [.move (plc 3),
                      .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                                  val := .zeroSized },
                      .copy (plc 2)]
                     (plc 0) (.some 1) .continue_
                 span := "ces_call" }
             isCleanup := false },
           retBlock] }
    runWith caller [.scalar ⟨5, 8⟩, fnPtrVal] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath (.fnPtr [.uint .u64] u32K .safe .rust)] =
      .ub := by
  rfl

/-- C10 on `tailCall`: forged `(N + 1)`-arg tail call to non-capturing closure and tail call to capturing closure both fault with `.ub`. -/
theorem tail_call_forged_env_and_capturing_is_ub :
    (runWith (tailEnvPtrCaller (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust) (.ref .not sharedClo))
       [fnPtrVal, envScalar, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body]
       [entry sharedPath (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust)],
     runWith (tailPtrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body]
       [entry capPath fnU32]) =
      (.ub, .ub) := by
  rfl

/-- `tailCall` through a closure pointer preserves frame-deallocation protector-conflict `.ub`. -/
theorem tail_call_protector_conflict_is_ub :
    let caller := tailPtrCaller fnU32
    let st : MirExecState :=
      .running
        { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocalsAux 0 caller.localDecls [fnPtrVal, u32v 5] }
          memory :=
            { memWith caller [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] [entry sharedPath fnU32] with
              borrows :=
                [{ tag := 1
                   targetLocal := 2
                   targetProjection := .nil
                   perm := .unique
                   rangeOffset := 0
                   rangeLen := 4
                   protector := .some 1
                   parentTag := .none
                   targetFrameDepth := 0
                   allocDead := false }]
              activeProtectors := [1]
              nextTag := 2
              nextProtector := 2 } }
    run 400 caller st = .ub := by
  rfl

/-- Unlinked closure coercion still rejects non-Rust target ABI (`extern "C"`) with `.ub`. -/
theorem coerce_unlinked_extern_c_is_ub :
    coerce "ClosureFnPointer(Safe)" sharedClo (.aggregate 0 .nil) (.fnPtr [u32K] u32K .safe .c) [] =
      .ub := by
  rfl

/-- Real-captured 2-level nested closure-to-`fn`-pointer call: `((10 ^ 3) ^ 7) + 1 = 15` (matches Miri). -/
theorem nested_fnptr_is_15 :
    runWith V08.Mir.ClosureExtended.nested_fnptr.body [u32v 10]
      [V08.Mir.ClosureExtended.nested_fnptr_closure_0.body,
       V08.Mir.ClosureExtended.nested_fnptr_closure_0_closure_0.body] =
      .normalScalar 15 4 := by
  rfl

/-- Real-captured concrete trait-impl closure-to-`fn`-pointer call: `(10 + 5) ^ 19 = 28` (matches Miri). -/
theorem concrete_trait_impl_closure_is_28 :
    runWith V08.Mir.ClosureExtended.call_concrete_trait_impl.body [u32v 10]
      [V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute.body,
       V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0.body] =
      .normalScalar 28 4 := by
  rfl

/-- C5 on real-captured default trait method: its closure inherits `Self` (`typeParamCount = 1`), so reification fails closed `.unsupported` (never `.ub`). -/
theorem default_trait_method_closure_is_unsupported :
    runWith V08.Mir.ClosureExtended.call_default_trait_closure.body [u32v 10]
      [V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute.body,
       V08.Mir.ClosureExtended.BoxedVal_as_Compute_compute_closure_0.body,
       V08.Mir.ClosureExtended.Compute_compute_default.body,
       V08.Mir.ClosureExtended.Compute_compute_default_closure_0.body] =
      .unsupported := by
  rfl

/-- Real-captured `ClosureFnPointer` -> `FnPtrToPtr` -> `Transmute` -> indirect call roundtrip: `10 ^ 31 = 21` (matches Miri). -/
theorem fn_ptr_transmute_roundtrip_is_21 :
    runWith V08.Mir.ClosureExtended.fn_ptr_transmute_roundtrip.body [u32v 10]
      [V08.Mir.ClosureExtended.fn_ptr_transmute_roundtrip_closure_0.body] =
      .normalScalar 21 4 := by
  rfl

/-- Tree Borrows compatibility: a non-capturing closure body beginning with `Retag(FnEntry, _1)` succeeds when entered with the synthesized ZST reference `.scalar ⟨1, 8⟩`. -/
theorem closure_body_fn_entry_retag_succeeds :
    let base := V08.Mir.ClosureMatrix.fn_shared_closure_0.body
    let retagBody :=
      { base with
        basicBlocks :=
          match base.basicBlocks with
          | bb0 :: rest =>
            { bb0 with
              statements :=
                { kind := .retag .fnEntry (plc 1), span := "retag_env" } :: bb0.statements } :: rest
          | .nil => .nil }
    runWith V08.Mir.ClosureMatrix.fn_shared.body [u32v 5] [retagBody] =
      .normalScalar 22 4 := by
  rfl

/-- Forged `ClosureFnPointer(Safe)` targeting a generic non-closure `fn` item faults with `.ub` (never `.unsupported`). -/
theorem coerce_generic_non_closure_is_ub :
    let genFn : CapturedMir :=
      { V08.Mir.ClosureMatrix.ct_add.body with
        defPath := "tests::gen_fn"
        typeParamCount := 1 }
    coerce "ClosureFnPointer(Safe)" (.closure "tests::gen_fn" .nil) (.aggregate 0 .nil) fnU32 [genFn] =
      .ub := by
  rfl

/-- C5 precedence on a forged linked body that is both capturing and generic (`typeParamCount = 1`): reification and an indirect call through a pointer to it fail closed with `.unsupported`, while the same capturing body without type parameters is `.ub` at both sites. -/
theorem generic_capturing_body_is_unsupported_not_ub :
    let genCap : CapturedMir :=
      { V08.Mir.ClosureMatrix.capturing_direct_closure_0.body with typeParamCount := 1 }
    (coerce "ClosureFnPointer(Safe)" (.closure capPath .nil) (.aggregate 0 .nil) fnU32 [genCap],
     coerce "ClosureFnPointer(Safe)" (.closure capPath .nil) (.aggregate 0 .nil) fnU32
       [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [genCap] [entry capPath fnU32],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body]
       [entry capPath fnU32]) =
      (.unsupported, .ub, .unsupported, .ub) := by
  rfl

/-- Inline `const_eval_select` rejects a forged `.unit` value in a `fn`-pointer local even when `target.typeArgs[2]` names a valid closure. -/
theorem inline_ces_forged_unit_with_fnptr_operand_ty_is_ub :
    let caller :=
      { V08.Mir.ClosureMatrix.fn_shared.body with
        defPath := "tests::ces_forged_unit_fnptr_ty"
        argCount := 2
        localDecls := [decl u32K 0, decl u32K 0, decl fnU32 1, decl (.tuple [u32K]) 0]
        basicBlocks :=
          [{ statements :=
               [{ kind := .storageLive 3, span := "ces_live" },
                { kind := .assign (plc 3) (.aggregate .tuple [.copy (plc 1)]), span := "ces_args" }]
             terminator :=
               { kind :=
                   .call
                     (.constant
                       { ty := { kind := .fnDef "core::intrinsics::const_eval_select" (cesTyArgs sharedClo)
                                 layoutIdx := 2 }
                         val := .zeroSized })
                     [.move (plc 3),
                      .constant { ty := { kind := .fnDef "closure_matrix::ct_add" .nil, layoutIdx := 2 }
                                  val := .zeroSized },
                      .copy (plc 2)]
                     (plc 0) (.some 1) .continue_
                 span := "ces_call" }
             isCleanup := false },
           retBlock] }
    runWith caller [u32v 5, .unit] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body] =
      .ub := by
  rfl

/-- `unpackConstEvalSelectArgs?` accepts a zero-sized tuple containing a non-capturing closure and rejects a capturing closure. -/
theorem unpack_ces_zst_closure_tuple :
    (unpackConstEvalSelectArgs? .unit (.some (.tuple [.closure "tests::c" .nil])),
     unpackConstEvalSelectArgs? .unit (.some (.tuple [.closure "tests::c" [u32K]]))) =
      (.some [.unit], .none) := by
  rfl

/-- Coercion-tag/callee-kind mismatches all fault with `.ub`: `ReifyFnPointer(Safe)` on a closure type, `ClosureFnPointer(Safe)` on a `fnDef` type, and forged `ReifyFnPointer(Safe)` on a `fnDef` naming a linked closure body even with an `(N + 1)`-arg signature. -/
theorem coerce_wrong_coercion_kind_is_ub :
    (coerce "ReifyFnPointer(Safe)" sharedClo (.aggregate 0 .nil) fnU32 [V08.Mir.ClosureMatrix.fn_shared_closure_0.body],
     coerce "ClosureFnPointer(Safe)" (.fnDef "closure_matrix::ct_add" .nil) .unit fnU32 [V08.Mir.ClosureMatrix.ct_add.body],
     coerce "ReifyFnPointer(Safe)" (.fnDef sharedPath .nil) .unit
       (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust)
       [V08.Mir.ClosureMatrix.fn_shared_closure_0.body]) =
      (.ub, .ub, .ub) := by
  rfl

/-- Inline `const_eval_select` rejects a forged `.closure` runtime target naming a linked non-closure `fn` item with `.ub` (never executing it and never returning `.unsupported` when generic). -/
theorem inline_ces_forged_closure_ty_on_non_closure_is_ub :
    let genFn : CapturedMir :=
      { V08.Mir.ClosureMatrix.ct_add.body with
        defPath := "tests::gen_fn"
        typeParamCount := 1 }
    (runWith (cesCaller (.closure "closure_matrix::ct_add" .nil)) [u32v 5, .aggregate 0 .nil]
       [V08.Mir.ClosureMatrix.ct_add.body],
     runWith (cesCaller (.closure "tests::gen_fn" .nil)) [u32v 5, .aggregate 0 .nil]
       [genFn]) =
      (.ub, .ub) := by
  rfl

/-- C5 precedence on inline `const_eval_select` with a linked generic capturing closure body (`typeParamCount = 1`): `.unsupported`, while the non-generic capturing body with forged `.closure capPath .nil` faults with `.ub`. -/
theorem inline_ces_generic_capturing_is_unsupported_not_ub :
    let genCap : CapturedMir :=
      { V08.Mir.ClosureMatrix.capturing_direct_closure_0.body with typeParamCount := 1 }
    (runWith (cesCaller (.closure capPath .nil)) [u32v 5, .aggregate 0 .nil] [genCap],
     runWith (cesCaller (.closure capPath .nil)) [u32v 5, .aggregate 0 .nil]
       [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body]) =
      (.unsupported, .ub) := by
  rfl

/-- Untyped `FnPtrEntry` (`fnSig = .none`) targeting a closure body: `N`-arg Rust-ABI call dispatches (`22`), while forged `(N + 1)`-arg call, capturing body, and non-Rust ABI body all fault with `.ub` (C10 without `fnSig`). -/
theorem untyped_fnptr_entry_closure_dispatch_and_c10 :
    let untypedEntry (p : DefPath) : FnPtrEntry :=
      { allocId := 65536, defPath := p, typeArgs := .nil, fnSig := .none }
    let cAbiClosure :=
      { V08.Mir.ClosureMatrix.fn_shared_closure_0.body with
        fnAbi := { V08.Mir.ClosureMatrix.fn_shared_closure_0.body.fnAbi with conv := .c } }
    (runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body]
       [untypedEntry sharedPath],
     runWith (envPtrCaller (.fnPtr [.ref .not sharedClo, u32K] u32K .safe .rust) (.ref .not sharedClo))
       [fnPtrVal, envScalar, u32v 5] [V08.Mir.ClosureMatrix.fn_shared_closure_0.body]
       [untypedEntry sharedPath],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [V08.Mir.ClosureMatrix.capturing_direct_closure_0.body]
       [untypedEntry capPath],
     runWith (ptrCaller fnU32) [fnPtrVal, u32v 5] [cAbiClosure]
       [untypedEntry sharedPath]) =
      (.normalScalar 22 4, .ub, .ub, .ub) := by
  rfl

end Anneal.ClosureFnPtrTests.V08

/-! ## 7. Axiom audit

Every declaration added by this file (the embedded `Mir.*` captures, the test-local
`V2026_08_01` stepper port, and all `Anneal.ClosureFnPtrTests.*` witnesses) is checked:
no `unsafe` declaration, and every axiom used is in `{propext, Classical.choice,
Quot.sound}` (so no `sorryAx`, no `Lean.ofReduceBool` / `native_decide`). Fails unless at
least 150 theorems are audited, so the audit cannot pass vacuously. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut decls : Nat := 0
  let mut theorems : Nat := 0
  for (n, ci) in env.constants.map₂.toList do
    if (`Anneal.ClosureFnPtrTests).isPrefixOf n || (`Mir).isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} depends on disallowed axiom {a}"
      decls := decls + 1
      if ci matches .thmInfo _ then
        theorems := theorems + 1
  if theorems < 150 then
    throwError "axiom audit covered only {theorems} theorems (expected at least 150)"
  logInfo m!"axiom audit passed: {decls} declarations ({theorems} theorems)"
