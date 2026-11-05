import Trusted

namespace Mir.FuchsiaUsercopy.atomic_load_u32_unpack

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `fuchsia_usercopy::atomic_load_u32_unpack`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=4, align=4
-- TypeLayout[2]: size=8, align=4
-- TypeLayout[3]: size=8, align=8
-- TypeLayout[4]: size=8, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 1 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))) }

-- bb0: _2 = Le(copy _1, const 4294967295_u64); switchInt(move _2) -> [0: bb2, otherwise: bb1]
-- bb1: _3 = copy _1 as u32 (IntToInt); _0 = (const true, move _3); goto -> bb3
-- bb2: _0 = (const false, const 0_u32); goto -> bb3
-- bb3: return
def body : CapturedMir :=
  {
    defPath := "fuchsia_usercopy::atomic_load_u32_unpack",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons RigidTy.bool (List.cons (RigidTy.uint UintTy.u32) List.nil))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u64), layoutIdx := 3 }, debugName := (Option.some "value_or_error") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.le (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u64), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4294967295, sizeBytes := 8 })) }))), span := "src/lib.rs:148:8: 148:37" } List.nil))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 2, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:148:8: 148:37" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.cast CastKind.intToInt (Operand.copy { local_ := 1, projection := List.nil }) { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 })), span := "src/lib.rs:149:16: 149:37" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }) (List.cons (Operand.move { local_ := 3, projection := List.nil }) List.nil)))), span := "src/lib.rs:149:9: 149:38" } List.nil)), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:148:5: 152:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple (List.cons (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:151:9: 151:19" } List.nil), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:148:5: 152:6" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:153:2: 153:2" }, isCleanup := false } List.nil)))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.pair }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.FuchsiaUsercopy.atomic_load_u32_unpack
