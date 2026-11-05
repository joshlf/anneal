import Trusted

namespace Mir.WireframeDemo.wire_protocol_version

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::wire_protocol_version`. -/

-- TypeLayout[0]: size=1, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = const WIRE_VERSION_V1; return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::wire_protocol_version",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } List.nil),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }))), span := "src/lib.rs:71:5: 71:20" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:72:2: 72:2" }, isCleanup := false } List.nil),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.wire_protocol_version
