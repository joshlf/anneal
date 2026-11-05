import Trusted

namespace Mir.WireframeDemo.is_valid_payload_len

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::is_valid_payload_len`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=2, align=2
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: _0 = Le(copy _1, const 1024_u16); return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::is_valid_payload_len",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.model,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 1 }, debugName := (Option.some "len") } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.le (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1024, sizeBytes := 2 })) }))), span := "src/lib.rs:78:5: 78:16" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:79:2: 79:2" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.is_valid_payload_len
