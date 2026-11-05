import Trusted

namespace Mir.WireframeDemo.parse_compression_flag

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::parse_compression_flag`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=1, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: _2 = BitAnd(copy _1, const 1_u8); _0 = Ne(move _2, const 0_u8); return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::parse_compression_flag",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 1 }, debugName := (Option.some "flags_byte") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 1 }, debugName := Option.none } List.nil))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }))), span := "src/lib.rs:179:5: 179:21" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.ne (Operand.move { local_ := 2, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 })) }))), span := "src/lib.rs:179:5: 179:26" } List.nil))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:180:2: 180:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.parse_compression_flag
