import Trusted

namespace Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `fuchsia_usercopy::fidl_pointer_is_encoded_present`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=1, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)) List.nil))), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: _2 = Eq(copy _1, const 0_u64); switchInt(move _2) -> [0: bb2, otherwise: bb1]
-- bb1: _0 = core::option::Option::<bool>::Some(const false); goto -> bb5
-- bb2: _3 = Eq(copy _1, const core::num::<impl u64>::MAX); switchInt(move _3) -> [0: bb4, otherwise: bb3]
-- bb3: _0 = core::option::Option::<bool>::Some(const true); goto -> bb5
-- bb4: _0 = core::option::Option::<bool>::None; goto -> bb5
-- bb5: return
def body : CapturedMir :=
  {
    defPath := "fuchsia_usercopy::fidl_pointer_is_encoded_present",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "core::option::Option" (List.cons RigidTy.bool List.nil)), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u64), layoutIdx := 1 }, debugName := (Option.some "encoded_u64") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 2 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u64), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:209:8: 209:24" } List.nil))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 2, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:209:8: 209:24" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 1 Option.none) (List.cons (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 })) }) List.nil))), span := "src/lib.rs:210:9: 210:20" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:209:5: 215:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u64), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 18446744073709551615, sizeBytes := 8 })) }))), span := "src/lib.rs:211:15: 211:38" } List.nil), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 4) List.nil), otherwise := 3 }), span := "src/lib.rs:211:15: 211:38" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 1 Option.none) (List.cons (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }) List.nil))), span := "src/lib.rs:212:9: 212:19" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:211:12: 215:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "core::option::Option" 0 Option.none) List.nil)), span := "src/lib.rs:214:9: 214:13" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:211:12: 215:6" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:216:2: 216:2" }, isCleanup := false } List.nil)))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)) List.nil))), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present
