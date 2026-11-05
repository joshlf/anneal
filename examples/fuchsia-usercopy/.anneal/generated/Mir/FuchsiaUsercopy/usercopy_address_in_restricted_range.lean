import Trusted

namespace Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `fuchsia_usercopy::usercopy_address_in_restricted_range`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: _4 = Eq(copy _1, const 0_usize); switchInt(move _4) -> [0: bb2, otherwise: bb1]
-- bb1: _0 = const false; goto -> bb5
-- bb2: _5 = Lt(copy _1, copy _2); switchInt(move _5) -> [0: bb4, otherwise: bb3]
-- bb3: _0 = const false; goto -> bb5
-- bb4: _0 = Lt(copy _1, copy _3); goto -> bb5
-- bb5: return
def body : CapturedMir :=
  {
    defPath := "fuchsia_usercopy::usercopy_address_in_restricted_range",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 3,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 1 }, debugName := (Option.some "addr") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 1 }, debugName := (Option.some "range_start") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 1 }, debugName := (Option.some "range_end") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 5), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.eq (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:66:8: 66:17" } List.nil))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 4, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:66:8: 66:17" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 })) }))), span := "src/lib.rs:67:16: 67:21" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "<dummy>" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 1, projection := List.nil }) (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:69:8: 69:26" } List.nil), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 5, projection := List.nil }) { branches := (List.cons (0, 4) List.nil), otherwise := 3 }), span := "src/lib.rs:69:8: 69:26" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 })) }))), span := "src/lib.rs:70:16: 70:21" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "<dummy>" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 1, projection := List.nil }) (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:72:5: 72:21" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:73:2: 73:2" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:73:2: 73:2" }, isCleanup := false } List.nil)))))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil))), ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range
